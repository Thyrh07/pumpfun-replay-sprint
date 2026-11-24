// Fresh-launch breakout bot for the pump.fun replay (paper, 10 SOL).
//
// Idea: most pump.fun coins die flat, but a large minority pump 1.5x-15x within
// minutes of launch and then retrace. This bot only buys FRESH curves (under
// ~4 minutes old) while early buy pressure is still accelerating, sizes small,
// and exits in stages: half at +60%, the rest at +150% or on a trailing stop,
// with a hard stop at -30% and a time stop. It never pyramids, never chases a
// coin that already ran far, and never holds a flat coin overnight.
//
// Why fresh, not mature: by the time a curve is 500+ slots old the easy move is
// usually gone; the data's 35 completions all ran 14.7x from creation, and 479
// of 1222 dev-window coins touched >=1.5x at some point while only 46 ended
// there — the money is in catching the move early and selling into it, not in
// holding to the close.
//
// Fees: ~1.25% curve fee per side plus ~0.000105 SOL tx fee per order, so a
// round trip costs ~2.7% on a 0.1 SOL stake. Every exit level sits far above
// that. Guardrails: at least 20 distinct coins with >=0.01 SOL round trips,
// max drawdown 50%, max 5 open positions.
//
// Deterministic by construction: no clock, no randomness, no environment reads;
// iteration only over insertion-ordered maps fed by the batch stream. Slot and
// block_time come from the replay data itself.

import {
  LAMPORTS_PER_SOL,
  runBot,
  type Batch,
  type BotState,
  type OrderInput,
  type Pubkey,
} from './vendor/makefun-bot.ts';

const LAMPORTS = 1e9;
const CURVE_FEE = 0.0125; // 95bps protocol + 30bps creator
const TX_SOL = 0.000105; // base 5000 + priority 100000 lamports, per order

// Entry: fresh breakout window.
const ENTRY_WINDOW = 40; // slots of tape to judge
const MAX_AGE = 240; // slots since CreateEvent; older coins are not fresh
const MIN_BUYS = 3; // buy trades in the window
const MIN_BUYERS = 3; // distinct buying wallets in the window
const MIN_NET_SOL = 0.3; // net buy SOL (buys minus sells) in the window
const STRONG_NET_SOL = 1.5; // net inflow that earns the bigger stake
const STRONG_BUYERS = 6;
const MIN_UP = 0.08; // price now vs window-start price, minus 1
const NEAR_HIGH = 0.95; // price now at least this share of the window high
const MAX_DOMINANCE = 0.7; // largest single buyer share of window buy SOL
const MIN_RQ_SOL = 0.5; // real SOL reserve at entry
const MAX_RQ_SOL = 40;
const STAKE_SOL = 0.1;
const STRONG_STAKE_SOL = 0.2;
const MIN_BUY_SOL = 0.01;
const BUY_SLIP_BPS = 1000;
const SELL_SLIP_BPS = 10_000;

// Exits.
const TP1 = 1.6; // sell half at +60% of cost
const TP2 = 2.5; // sell the rest at +150% of cost
const TRAIL_ARM = 1.3; // trailing stop arms once value hits cost * this
const TRAIL = 0.25; // sell when value falls this far below its peak
const STOP_LOSS = 0.7; // sell everything below cost * this
const MAX_HOLD = 1200; // slots; time stop unless already up
const HOLD_IF_UP = 1.1;
const COOLDOWN = 100; // slots after an exit before re-entering a coin
const MAX_ENTRIES = 2;
const MAX_EXPOSURE_SOL = 1.0; // most SOL at cost across positions at once

// Pace fallback: keep the 20-coin guardrail safe even if the strict signal
// goes quiet. Elapsed share is block time since the first batch over 24h.
const PACE_TARGET_COINS = 25;
const PACE_WINDOW_SECS = 86_400;
const FALLBACK_STAKE_SOL = 0.01;
const FALLBACK_TP = 1.3;
const FALLBACK_STOP = 0.8;
const FALLBACK_HOLD = 600;

interface Trade {
  slot: number;
  buy: boolean;
  sol: number;
  user: string;
  price: number;
}

interface Tape {
  created: number | null;
  trades: Trade[];
  entries: number;
  lastExit: number;
}

interface Held {
  opened: number;
  /** Best value/cost ratio seen. Ratios stay continuous across a partial
      sell (both value and cost halve), so the trailing stop never fires on
      the sell itself. */
  peakRatio: number;
  stage: 0 | 1; // 0 = full size, 1 = half already sold at TP1
  filled: boolean;
  fallback: boolean;
}

const tapes = new Map<Pubkey, Tape>();
const held = new Map<Pubkey, Held>();
let myFills = 0;
const myCoins = new Set<Pubkey>();
let firstTime: number | null = null;
let lastTime: number | null = null;

const tapeOf = (mint: Pubkey): Tape => {
  let t = tapes.get(mint);
  if (t === undefined) {
    t = { created: null, trades: [], entries: 0, lastExit: -1e12 };
    tapes.set(mint, t);
  }
  return t;
};

/** Price of one token in SOL from virtual reserves. */
const priceOf = (vq: number, vt: number): number => (vt > 0 ? vq / vt / LAMPORTS : 0);

/** Estimated SOL received for selling `tokens` now (curve fee + tx fee off). */
const sellValue = (tokens: number, vq: number, vt: number): number =>
  ((tokens * vq) / (vt + tokens) / LAMPORTS) * (1 - CURVE_FEE) - TX_SOL;

/** Fresh-breakout entry signal on a tape at slot `now`. */
const entrySignal = (t: Tape, now: number, rqSol: number): { ok: boolean; strong: boolean } => {
  const no = { ok: false, strong: false };
  if (rqSol < MIN_RQ_SOL || rqSol > MAX_RQ_SOL) return no;
  if (t.created === null || now - t.created > MAX_AGE) return no;
  const from = now - ENTRY_WINDOW;
  let buySol = 0;
  let sellSol = 0;
  let buys = 0;
  let startPrice = -1;
  let high = 0;
  let last = 0;
  const byUser = new Map<string, number>();
  for (const tr of t.trades) {
    if (tr.slot <= from) {
      startPrice = tr.price;
      continue;
    }
    if (startPrice < 0) startPrice = tr.price;
    if (tr.buy) {
      buySol += tr.sol;
      buys++;
      byUser.set(tr.user, (byUser.get(tr.user) ?? 0) + tr.sol);
    } else {
      sellSol += tr.sol;
    }
    if (tr.price > high) high = tr.price;
    last = tr.price;
  }
  if (buys < MIN_BUYS || byUser.size < MIN_BUYERS) return no;
  const net = buySol - sellSol;
  if (net < MIN_NET_SOL) return no;
  if (startPrice <= 0) return no;
  const up = last / startPrice - 1;
  if (up < MIN_UP) return no;
  if (last < high * NEAR_HIGH) return no;
  let top = 0;
  for (const v of byUser.values()) if (v > top) top = v;
  if (top > MAX_DOMINANCE * buySol) return no;
  return { ok: true, strong: net >= STRONG_NET_SOL && byUser.size >= STRONG_BUYERS };
};

await runBot({
  onBatch(state: BotState, batch: Batch): OrderInput[] {
    const now = batch.slot;
    const traded = new Set<Pubkey>();
    for (const f of batch.fills) {
      if (f.status === 'filled' && !f.client_id.startsWith('_')) {
        myFills++;
        myCoins.add(f.mint);
      }
    }
    for (const e of batch.events) {
      if (e.block_time !== null) {
        if (firstTime === null) firstTime = e.block_time;
        if (lastTime === null || e.block_time > lastTime) lastTime = e.block_time;
      }
      if (e.event === 'CreateEvent') {
        tapeOf(e.mint).created = e.slot;
      } else if (e.event === 'TradeEvent') {
        const t = tapeOf(e.mint);
        t.trades.push({
          slot: e.slot,
          buy: e.is_buy,
          sol: Number(e.sol_amount) / LAMPORTS,
          user: e.user,
          price: priceOf(Number(e.virtual_quote_reserves), Number(e.virtual_token_reserves)),
        });
        traded.add(e.mint);
      }
    }
    // Prune tape history older than the longest lookback we use.
    const keep = Math.max(ENTRY_WINDOW, MAX_HOLD) + 5;
    for (const mint of traded) {
      const t = tapes.get(mint)!;
      let cut = 0;
      while (cut < t.trades.length && t.trades[cut]!.slot <= now - keep) cut++;
      if (cut > 0) t.trades.splice(0, cut);
    }

    const marks = new Map(batch.marks.map((m) => [m.mint, m] as const));
    const pendingByMint = new Map<Pubkey, number>();
    for (const po of state.pending.values()) {
      pendingByMint.set(po.order.mint, (pendingByMint.get(po.order.mint) ?? 0) + 1);
    }
    const orders: OrderInput[] = [];
    const cap = state.hello.caps.max_orders_per_batch;
    const tx = Number(state.txFeeLamports()) / LAMPORTS;

    // Exits first: staged take-profit, trailing stop, hard stop, time stop.
    for (const [mint, h] of held) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) {
          held.delete(mint);
          const t = tapeOf(mint);
          if (h.filled) t.lastExit = now;
          else t.entries--;
        }
        continue;
      }
      h.filled = true;
      if (curve === undefined || curve.complete) continue;
      const mk = marks.get(mint);
      const vq = mk ? Number(mk.virtual_quote_reserves) : Number(curve.virtual_quote_reserves);
      const vt = mk ? Number(mk.virtual_token_reserves) : Number(curve.virtual_token_reserves);
      const tokens = Number(pos.token_amount);
      const value = sellValue(tokens, vq, vt);
      const cost = Number(pos.cost_lamports) / LAMPORTS;
      const ratio = cost > 0 ? value / cost : 0;
      if (ratio > h.peakRatio) h.peakRatio = ratio;
      const tp1 = h.fallback ? FALLBACK_TP : TP1;
      const tp2 = h.fallback ? FALLBACK_TP : TP2;
      const stop = h.fallback ? FALLBACK_STOP : STOP_LOSS;
      const maxHold = h.fallback ? FALLBACK_HOLD : MAX_HOLD;
      let sellAll = false;
      let sellHalf = false;
      if (ratio >= tp2) sellAll = true;
      else if (h.stage === 0 && ratio >= tp1) sellHalf = true;
      else if (ratio < stop) sellAll = true;
      else if (!h.fallback && h.peakRatio >= TRAIL_ARM && ratio < h.peakRatio * (1 - TRAIL)) sellAll = true;
      else if (now - h.opened > maxHold && ratio < HOLD_IF_UP) sellAll = true;
      if (!sellAll && !sellHalf) continue;
      if (pendingByMint.has(mint)) {
        let sellPending = false;
        for (const po of state.pending.values()) {
          if (po.order.mint === mint && po.order.side === 'sell') sellPending = true;
        }
        if (sellPending) continue;
      }
      if (orders.length >= cap) break;
      const amount = sellAll ? pos.token_amount : BigInt(tokens / 2);
      orders.push({ side: 'sell', mint, token_amount: amount, max_slippage_bps: SELL_SLIP_BPS });
      if (sellHalf) h.stage = 1;
    }

    // Entries: fresh breakout first, pace fallback when the coin count lags.
    let free = Number(state.freeCashLamports()) / LAMPORTS;
    let slotsLeft = state.hello.caps.max_open_positions - state.committedPositionCount();
    let exposure = 0;
    for (const [mint] of held) {
      const pos = state.positions.get(mint);
      exposure += pos ? Number(pos.cost_lamports) / LAMPORTS : 0;
    }
    let behindPace = false;
    if (firstTime !== null && lastTime !== null) {
      const pace = Math.min(1, (lastTime - firstTime) / PACE_WINDOW_SECS);
      behindPace = myCoins.size < Math.ceil(PACE_TARGET_COINS * pace);
    }
    for (const mint of traded) {
      if (orders.length >= cap) break;
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      if (pendingByMint.has(mint) || held.has(mint)) continue;
      const t = tapes.get(mint)!;
      if (t.entries >= MAX_ENTRIES || now - t.lastExit < COOLDOWN) continue;
      const rqSol = Number(curve.real_quote_reserves) / LAMPORTS;
      const sig = entrySignal(t, now, rqSol);
      let want = 0;
      let fallback = false;
      if (sig.ok) {
        want = sig.strong ? STRONG_STAKE_SOL : STAKE_SOL;
      } else if (behindPace && slotsLeft > 0) {
        // Pace fallback: any fresh coin with a couple of buys and a usable cap.
        if (t.created === null || now - t.created > MAX_AGE) continue;
        let buys = 0;
        for (const tr of t.trades) if (tr.slot > now - ENTRY_WINDOW && tr.buy) buys++;
        if (buys < 2) continue;
        want = FALLBACK_STAKE_SOL;
        fallback = true;
      } else {
        continue;
      }
      if (slotsLeft <= 0) continue;
      const capSol = Math.floor(Number(state.maxBuyLamports(mint))) / LAMPORTS;
      let amount = Math.min(capSol, want, MAX_EXPOSURE_SOL - exposure);
      if (amount > free - tx) amount = free - tx;
      if (amount < MIN_BUY_SOL) continue;
      const lamports = BigInt(Math.floor(amount * LAMPORTS));
      orders.push({ side: 'buy', mint, quote_lamports: lamports, max_slippage_bps: BUY_SLIP_BPS });
      free -= amount + tx;
      exposure += amount;
      held.set(mint, { opened: now, peakRatio: 0, stage: 0, filled: false, fallback });
      t.entries++;
      slotsLeft--;
    }
    return orders;
  },
});
