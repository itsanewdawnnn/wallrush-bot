(() => {
  const BUDGET_MS = 3000;
  const POLL_MS = 400;
  const COOLDOWN_MS = 1500;
  const $ = (id) => document.getElementById(id);
  let enabled = false;
  let busy = false;

  function engineMain() {
    const MATE = 1000000;
    const TT_SIZE = 1 << 20;
    const ttChk = new Int32Array(TT_SIZE);
    const ttScore = new Int32Array(TT_SIZE);
    const ttMove = new Int16Array(TT_SIZE);
    const ttDepth = new Int8Array(TT_SIZE);
    const ttFlag = new Int8Array(TT_SIZE);

    const STEP = 100;
    const TEMPO = 30;
    const WALL_VALUE = 25;
    const NEAR_WIN = 5000;

    let seed = 0x5eed1234;
    const rand = () => {
      seed = (seed + 0x6D2B79F5) | 0;
      let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return (t ^ (t >>> 14)) | 0;
    };
    const table = (n) => Array.from({ length: n }, rand);
    const ZH1 = table(200), ZH2 = table(200), ZV1 = table(200), ZV2 = table(200);
    const ZP1 = [table(200), table(200)], ZP2 = [table(200), table(200)];
    const ZL1 = [table(20), table(20)], ZL2 = [table(20), table(20)];
    const ZT1 = rand(), ZT2 = rand();

    let W = 9, H = 9, N = 81, S = 64;
    let goal = [0, 8];
    let nbr = new Int16Array(81 * 4);
    let rowOf = new Int8Array(81);
    let blk = new Uint8Array(81);
    let hw = new Uint8Array(64);
    let vw = new Uint8Array(64);
    let pos = [0, 0];
    let left = [10, 10];
    let turn = 0;
    let k1 = 0, k2 = 0;
    let queue = new Int16Array(81);
    let nodes = 0, deadline = 0, timedOut = false;
    let rootMove = null;
    const seen = new Set();
    let prevWalls = 0;
    let maps = [];
    let scratchA = null, scratchB = null;

    const now = () => (typeof performance !== 'undefined' ? performance.now() : Date.now());

    const setupBoard = (cols, rows) => {
      W = cols; H = rows; N = W * H; S = (W - 1) * (H - 1);
      nbr = new Int16Array(N * 4).fill(-1);
      rowOf = new Int8Array(N);
      for (let r = 0; r < H; r++) {
        for (let c = 0; c < W; c++) {
          const i = r * W + c;
          rowOf[i] = r;
          if (r > 0) nbr[i * 4] = i - W;
          if (r < H - 1) nbr[i * 4 + 1] = i + W;
          if (c > 0) nbr[i * 4 + 2] = i - 1;
          if (c < W - 1) nbr[i * 4 + 3] = i + 1;
        }
      }
      blk = new Uint8Array(N);
      hw = new Uint8Array(S);
      vw = new Uint8Array(S);
      queue = new Int16Array(N);
      maps = [];
      scratchA = new Int16Array(N);
      scratchB = new Int16Array(N);
    };

    const mapsAt = (ply) => {
      while (maps.length <= ply) maps.push([new Int16Array(N), new Int16Array(N), new Int16Array(N)]);
      return maps[ply];
    };

    const bfsRow = (row, out) => {
      out.fill(-1);
      let head = 0, tail = 0;
      const base = row * W;
      for (let c = 0; c < W; c++) { out[base + c] = 0; queue[tail++] = base + c; }
      while (head < tail) {
        const cur = queue[head++];
        const b = blk[cur];
        const d1 = out[cur] + 1;
        const o = cur * 4;
        for (let d = 0; d < 4; d++) {
          if ((b >> d) & 1) continue;
          const nx = nbr[o + d];
          if (nx < 0 || out[nx] !== -1) continue;
          out[nx] = d1;
          queue[tail++] = nx;
        }
      }
    };

    const bfsCell = (cell, out) => {
      out.fill(-1);
      let head = 0, tail = 0;
      out[cell] = 0;
      queue[tail++] = cell;
      while (head < tail) {
        const cur = queue[head++];
        const b = blk[cur];
        const d1 = out[cur] + 1;
        const o = cur * 4;
        for (let d = 0; d < 4; d++) {
          if ((b >> d) & 1) continue;
          const nx = nbr[o + d];
          if (nx < 0 || out[nx] !== -1) continue;
          out[nx] = d1;
          queue[tail++] = nx;
        }
      }
    };

    const wallCells = (i) => {
      const r = (i / (W - 1)) | 0, c = i % (W - 1);
      return r * W + c;
    };

    const setWall = (o, i, on) => {
      const a = wallCells(i);
      if (o === 0) {
        if (on) { blk[a] |= 2; blk[a + 1] |= 2; blk[a + W] |= 1; blk[a + W + 1] |= 1; hw[i] = 1; }
        else { blk[a] &= ~2; blk[a + 1] &= ~2; blk[a + W] &= ~1; blk[a + W + 1] &= ~1; hw[i] = 0; }
      } else if (on) { blk[a] |= 8; blk[a + W] |= 8; blk[a + 1] |= 4; blk[a + W + 1] |= 4; vw[i] = 1; }
      else { blk[a] &= ~8; blk[a + W] &= ~8; blk[a + 1] &= ~4; blk[a + W + 1] &= ~4; vw[i] = 0; }
    };

    const slotFree = (o, i) => {
      if (hw[i] || vw[i]) return false;
      const r = (i / (W - 1)) | 0, c = i % (W - 1);
      if (o === 0) return !(c > 0 && hw[i - 1]) && !(c < W - 2 && hw[i + 1]);
      return !(r > 0 && vw[i - (W - 1)]) && !(r < H - 2 && vw[i + (W - 1)]);
    };

    const pawnTargets = (p) => {
      const me = pos[p], op = pos[1 - p];
      const out = [];
      const b = blk[me];
      for (let d = 0; d < 4; d++) {
        if ((b >> d) & 1) continue;
        const n1 = nbr[me * 4 + d];
        if (n1 < 0) continue;
        if (n1 !== op) { out.push(n1); continue; }
        if (!((blk[n1] >> d) & 1)) {
          const n2 = nbr[n1 * 4 + d];
          if (n2 >= 0) { out.push(n2); continue; }
        }
        const s0 = d < 2 ? 2 : 0;
        for (let k = 0; k < 2; k++) {
          const pd = s0 + k;
          if ((blk[n1] >> pd) & 1) continue;
          const n3 = nbr[n1 * 4 + pd];
          if (n3 >= 0) out.push(n3);
        }
      }
      return out;
    };

    const stat = (dMeAfter, dOppAfter, leftMe, leftOpp) => {
      let s = (dMeAfter - dOppAfter) * STEP + TEMPO + (leftOpp - leftMe) * WALL_VALUE;
      if (dOppAfter <= 1) s += NEAR_WIN;
      return -s;
    };

    const genMoves = (ply, depth) => {
      const p = turn, q = 1 - p;
      const [mMe, mOpp, mFrom] = mapsAt(ply);
      bfsRow(goal[p], mMe);
      bfsRow(goal[q], mOpp);
      const dMe = mMe[pos[p]], dOpp = mOpp[pos[q]];
      const pm = [];
      const targets = pawnTargets(p);
      for (const t of targets) {
        const win = rowOf[t] === goal[p];
        pm.push({ t: 0, i: t, ord: -mMe[t], win, ev: win ? MATE : stat(mMe[t], dOpp, left[p], left[q]) });
      }
      pm.sort((a, b) => b.ord - a.ord);

      const wm = [];
      if (left[p] > 0) {
        bfsCell(pos[q], mFrom);
        const cap = ply === 0 ? 24 : depth >= 4 ? 10 : depth === 3 ? 8 : 6;
        for (let o = 0; o < 2; o++) {
          for (let i = 0; i < S; i++) {
            if (!slotFree(o, i)) continue;
            const a = wallCells(i);
            let e1a, e1b, e2a, e2b;
            if (o === 0) { e1a = a; e1b = a + W; e2a = a + 1; e2b = a + W + 1; }
            else { e1a = a; e1b = a + 1; e2a = a + W; e2b = a + W + 1; }
            const onPath = (x, y) => mFrom[x] >= 0 && mFrom[y] >= 0 &&
              (mFrom[x] + 1 + mOpp[y] === dOpp || mFrom[y] + 1 + mOpp[x] === dOpp);
            if (!onPath(e1a, e1b) && !onPath(e2a, e2b)) continue;
            setWall(o, i, true);
            bfsRow(goal[q], scratchA);
            const newOpp = scratchA[pos[q]];
            let ok = newOpp > dOpp;
            let newMe = dMe;
            if (ok) {
              const tight = Math.abs(mMe[e1a] - mMe[e1b]) === 1 || Math.abs(mMe[e2a] - mMe[e2b]) === 1;
              if (tight) {
                bfsRow(goal[p], scratchB);
                newMe = scratchB[pos[p]];
                if (newMe < 0) ok = false;
              }
            }
            setWall(o, i, false);
            if (!ok) continue;
            const net = (newOpp - dOpp) - (newMe - dMe);
            if (net < 1) continue;
            wm.push({ t: 1, o, i, ord: net * 1000 + (newOpp - dOpp), win: false, ev: stat(newMe, newOpp, left[p] - 1, left[q]) });
          }
        }
        wm.sort((a, b) => b.ord - a.ord);
        if (wm.length > cap) wm.length = cap;
      }
      const list = [];
      if (pm.length) list.push(pm[0]);
      for (const w of wm) list.push(w);
      for (let k = 1; k < pm.length; k++) list.push(pm[k]);
      if (ply === 0 && seen.size) {
        const fresh = list.filter((m) => {
          if (m.win) return true;
          make(m);
          const again = seen.has(k1);
          unmake(m);
          return !again;
        });
        if (fresh.length) return fresh;
      }
      return list;
    };

    const codeOf = (m) => (m.t === 0 ? m.i : N + m.o * S + m.i);

    const make = (m) => {
      const p = turn;
      if (m.t === 0) {
        const from = pos[p];
        k1 ^= ZP1[p][from] ^ ZP1[p][m.i] ^ ZT1;
        k2 ^= ZP2[p][from] ^ ZP2[p][m.i] ^ ZT2;
        pos[p] = m.i;
        m.from = from;
      } else {
        setWall(m.o, m.i, true);
        const z1 = m.o === 0 ? ZH1[m.i] : ZV1[m.i];
        const z2 = m.o === 0 ? ZH2[m.i] : ZV2[m.i];
        k1 ^= z1 ^ ZL1[p][left[p]] ^ ZL1[p][left[p] - 1] ^ ZT1;
        k2 ^= z2 ^ ZL2[p][left[p]] ^ ZL2[p][left[p] - 1] ^ ZT2;
        left[p]--;
      }
      turn = 1 - p;
    };

    const unmake = (m) => {
      const p = 1 - turn;
      if (m.t === 0) {
        const to = pos[p];
        k1 ^= ZP1[p][m.from] ^ ZP1[p][to] ^ ZT1;
        k2 ^= ZP2[p][m.from] ^ ZP2[p][to] ^ ZT2;
        pos[p] = m.from;
      } else {
        left[p]++;
        const z1 = m.o === 0 ? ZH1[m.i] : ZV1[m.i];
        const z2 = m.o === 0 ? ZH2[m.i] : ZV2[m.i];
        k1 ^= z1 ^ ZL1[p][left[p]] ^ ZL1[p][left[p] - 1] ^ ZT1;
        k2 ^= z2 ^ ZL2[p][left[p]] ^ ZL2[p][left[p] - 1] ^ ZT2;
        setWall(m.o, m.i, false);
      }
      turn = p;
    };

    const negamax = (depth, alpha, beta, ply) => {
      if ((++nodes & 255) === 0 && now() > deadline) timedOut = true;
      if (timedOut) return 0;
      const alpha0 = alpha;
      const idx = (k1 >>> 0) & (TT_SIZE - 1);
      let ttm = -1;
      if (ply > 0 && ttChk[idx] === k2 && ttDepth[idx] > 0) {
        ttm = ttMove[idx];
        if (ttDepth[idx] >= depth) {
          const f = ttFlag[idx], s = ttScore[idx];
          if (f === 0) return s;
          if (f === 1 && s >= beta) return s;
          if (f === -1 && s <= alpha) return s;
        }
      } else if (ttChk[idx] === k2 && ttDepth[idx] > 0) {
        ttm = ttMove[idx];
      }

      const moves = genMoves(ply, depth);
      if (!moves.length) return -MATE;
      if (ttm >= 0) {
        const at = moves.findIndex((m) => codeOf(m) === ttm);
        if (at > 0) { const [m] = moves.splice(at, 1); moves.unshift(m); }
      }

      let best = -Infinity;
      let bestCode = -1;
      let first = true;
      for (const m of moves) {
        let s;
        if (m.win) s = MATE - ply;
        else if (depth === 1) s = m.ev;
        else {
          make(m);
          if (first) s = -negamax(depth - 1, -beta, -alpha, ply + 1);
          else {
            s = -negamax(depth - 1, -alpha - 1, -alpha, ply + 1);
            if (s > alpha && s < beta && !timedOut) s = -negamax(depth - 1, -beta, -alpha, ply + 1);
          }
          unmake(m);
        }
        if (timedOut) return 0;
        first = false;
        if (s > best) {
          best = s;
          bestCode = codeOf(m);
          if (ply === 0) rootMove = m;
        }
        if (best > alpha) alpha = best;
        if (alpha >= beta) break;
      }
      ttChk[idx] = k2;
      ttScore[idx] = best;
      ttMove[idx] = bestCode;
      ttDepth[idx] = depth;
      ttFlag[idx] = best <= alpha0 ? -1 : best >= beta ? 1 : 0;
      return best;
    };

    const load = (state) => {
      const cols = state.cols || 9, rows = state.rows || 9;
      setupBoard(cols, rows);
      goal = state.mode === 'race' ? [0, 0] : [0, rows - 1];
      for (const w of state.walls) setWall(w.o === 'h' ? 0 : 1, w.r * (W - 1) + w.c, true);
      pos = state.pawns.map((p) => p.r * W + p.c);
      left = [state.left[0], state.left[1]];
      turn = state.turn;
      k1 = 0; k2 = 0;
      for (let i = 0; i < S; i++) {
        if (hw[i]) { k1 ^= ZH1[i]; k2 ^= ZH2[i]; }
        if (vw[i]) { k1 ^= ZV1[i]; k2 ^= ZV2[i]; }
      }
      for (let p = 0; p < 2; p++) {
        k1 ^= ZP1[p][pos[p]] ^ ZL1[p][left[p]];
        k2 ^= ZP2[p][pos[p]] ^ ZL2[p][left[p]];
      }
      if (turn) { k1 ^= ZT1; k2 ^= ZT2; }
    };

    const chooseMove = (state, opts = {}) => {
      if (state.walls.length < prevWalls || opts.newGame) seen.clear();
      prevWalls = state.walls.length;
      load(state);
      seen.add(k1);
      ttChk.fill(0); ttDepth.fill(0);
      nodes = 0; timedOut = false;
      const budget = opts.budgetMs || 1500;
      const start = now();
      deadline = start + budget;
      let best = null;
      let reached = 0;
      for (let depth = 1; depth <= (opts.maxDepth || 40); depth++) {
        rootMove = null;
        const score = negamax(depth, -Infinity, Infinity, 0);
        if (timedOut) {
          if (rootMove && best === null) best = rootMove;
          break;
        }
        best = rootMove;
        reached = depth;
        if (Math.abs(score) > MATE - 1000) break;
        if (now() - start > budget * 0.55) break;
      }
      chooseMove.last = { depth: reached, nodes, ms: Math.round(now() - start) };
      if (!best) return null;
      make(best);
      seen.add(k1);
      unmake(best);
      if (best.t === 0) return { type: 'pawn', r: rowOf[best.i], c: best.i % W };
      const r = (best.i / (W - 1)) | 0, c = best.i % (W - 1);
      return { type: 'wall', o: best.o === 0 ? 'h' : 'v', r, c };
    };

    return { chooseMove };
  }

  const WORKER_SRC = 'const engine=(' + engineMain.toString() + ')();'
    + 'onmessage=(e)=>{postMessage(engine.chooseMove(e.data.state,{budgetMs:e.data.budgetMs}));};';
  let worker = null;
  let mainEngine = null;

  const viaWorker = (state) => new Promise((resolve, reject) => {
    if (!worker) {
      worker = new Worker(URL.createObjectURL(new Blob([WORKER_SRC], { type: 'text/javascript' })));
    }
    worker.onmessage = (e) => resolve(e.data);
    worker.onerror = (e) => { worker = null; reject(e); };
    worker.postMessage({ state, budgetMs: BUDGET_MS });
  });

  const think = async (state) => {
    try {
      return await viaWorker(state);
    } catch {
      if (!mainEngine) mainEngine = engineMain();
      return mainEngine.chooseMove(state, { budgetMs: BUDGET_MS });
    }
  };

  const center = (el) => {
    const b = el.getBoundingClientRect();
    return { x: b.left + b.width / 2, y: b.top + b.height / 2 };
  };

  const readState = () => {
    const board = $('board');
    const chipMe = $('chip-me');
    const chipOpp = $('chip-opp');
    const quad = $('quad-row');
    if (!board || !chipMe || !chipMe.offsetParent || (quad && !quad.hidden)) return null;
    const cells = [...board.querySelectorAll('.cell')];
    if (!cells.length) return null;
    const rows = Math.max(...cells.map((c) => +c.dataset.vr)) + 1;
    const cols = Math.max(...cells.map((c) => +c.dataset.vc)) + 1;
    const race = rows !== cols;
    const me = board.classList.contains('my-red') ? 1 : 0;
    const flip = me === 1 && !race;
    const toLogical = (r, c) => (flip ? { r: rows - 1 - r, c: cols - 1 - c } : { r, c });

    const nearest = (el) => {
      const x = parseFloat(el.style.left);
      const y = parseFloat(el.style.top);
      let best = null;
      let bd = Infinity;
      for (const c of cells) {
        const d = (parseFloat(c.style.left) - x) ** 2 + (parseFloat(c.style.top) - y) ** 2;
        if (d < bd) { bd = d; best = c; }
      }
      return best;
    };
    const pawns = [];
    for (const color of ['blue', 'red']) {
      const el = board.querySelector('.pawn.' + color);
      if (!el || el.hidden) return null;
      const cell = nearest(el);
      pawns.push(toLogical(+cell.dataset.vr, +cell.dataset.vc));
    }

    const walls = [...board.querySelectorAll('.wall:not(.preview)')].map((el) => {
      const [r, c, o] = el.dataset.w.split(',');
      return { r: +r, c: +c, o };
    });

    let turn = null;
    if (chipMe.classList.contains('turn-active')) turn = me;
    else if (chipOpp && chipOpp.classList.contains('turn-active')) turn = 1 - me;
    if (turn === null) return null;

    const left = [];
    left[me] = +$('me-walls').textContent;
    left[1 - me] = +$('opp-walls').textContent;

    return {
      me, flip, rows, cols, cells,
      state: { mode: race ? 'race' : 'duel', cols, rows, pawns, walls, left, turn, winner: null },
    };
  };

  const fire = (target, type, x = 0, y = 0) =>
    target.dispatchEvent(new MouseEvent(type, { bubbles: true, cancelable: true, clientX: x, clientY: y, view: window }));

  const touch = (target, type, x, y) => {
    const t = new Touch({ identifier: 1, target, clientX: x, clientY: y });
    const list = type === 'touchend' ? [] : [t];
    target.dispatchEvent(new TouchEvent(type, {
      bubbles: true, cancelable: true, changedTouches: [t], touches: list, targetTouches: list,
    }));
  };

  const play = (ctx, move) => {
    const { cells, rows, cols, flip } = ctx;
    const cellAt = (r, c) => cells.find((el) => +el.dataset.vr === r && +el.dataset.vc === c);
    if (move.type === 'pawn') {
      const v = flip ? { r: rows - 1 - move.r, c: cols - 1 - move.c } : move;
      fire(cellAt(v.r, v.c), 'click');
      return;
    }
    const r = flip ? rows - 2 - move.r : move.r;
    const c = flip ? cols - 2 - move.c : move.c;
    const pts = [[r, c], [r, c + 1], [r + 1, c], [r + 1, c + 1]].map(([a, b]) => center(cellAt(a, b)));
    const x = pts.reduce((s, p) => s + p.x, 0) / 4;
    const y = pts.reduce((s, p) => s + p.y, 0) / 4;
    const handle = $(move.o === 'h' ? 'drag-h' : 'drag-v');
    if ('ontouchstart' in window) {
      const yy = y + cellAt(0, 0).getBoundingClientRect().width * 0.8;
      touch(handle, 'touchstart', x, yy);
      touch(document, 'touchmove', x, yy);
      touch(document, 'touchend', x, yy);
    } else {
      fire(handle, 'mousedown', x, y);
      fire(window, 'mousemove', x, y);
      fire(window, 'mouseup', x, y);
    }
  };

  const step = async () => {
    if (!enabled || busy) return;
    const ctx = readState();
    if (!ctx || ctx.state.turn !== ctx.me) return;
    busy = true;
    try {
      const move = await think(ctx.state);
      const now = readState();
      if (enabled && move && now && now.state.turn === now.me) play(now, move);
    } finally {
      setTimeout(() => { busy = false; }, COOLDOWN_MS);
    }
  };

  const button = document.createElement('button');
  button.style.cssText = 'position:fixed;left:8px;bottom:8px;z-index:99999;padding:6px 10px;border:0;border-radius:8px;'
    + 'font:600 13px system-ui,sans-serif;color:#fff;opacity:.85;cursor:pointer';
  const paint = () => {
    button.textContent = 'Bot: ' + (enabled ? 'NYALA' : 'MATI');
    button.style.background = enabled ? '#16a34a' : '#6b7280';
  };
  const toggle = () => { enabled = !enabled; paint(); };
  button.title = 'Nyalakan atau matikan bot (Alt+B)';
  button.addEventListener('click', toggle);
  document.addEventListener('keydown', (e) => {
    if (e.altKey && e.key.toLowerCase() === 'b') { e.preventDefault(); toggle(); }
  });
  paint();
  document.body.appendChild(button);
  setInterval(step, POLL_MS);
})();
