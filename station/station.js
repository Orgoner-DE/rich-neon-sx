(() => {
  const MAX_SEC = 2.2 * 3600;
  const WAV_MAX = 10 * 60;
  const POLY = 24;
  const NAMES = ["C","C#","D","D#","E","F","F#","G","G#","A","A#","B"];
  const OSCS = ["piano","ep","organ","strings","pad","brass","bass","pluck","saw","lead"];
  const PADS = [
    {name:"Kick", osc:"bass", n:36},
    {name:"Snare", osc:"pluck", n:50},
    {name:"Hat", osc:"saw", n:82},
    {name:"Grand", osc:"piano", n:60},
    {name:"EP", osc:"ep", n:64},
    {name:"Organ", osc:"organ", n:55},
    {name:"Air", osc:"pad", n:72},
    {name:"Lead", osc:"lead", n:76}
  ];
  const DEVICES = [
    {id:"eq", group:"Effekt", name:"EQ"},
    {id:"comp", group:"Effekt", name:"Kompressor"},
    {id:"filter", group:"Effekt", name:"Filter"},
    {id:"delay", group:"Effekt", name:"Delay"},
    {id:"hall", group:"Effekt", name:"Hall"},
    {id:"chorus", group:"Effekt", name:"Chorus"},
    {id:"drive", group:"Effekt", name:"Drive"},
    {id:"limit", group:"Effekt", name:"Limiter"},
    {id:"drums", group:"Drum-Sampler", name:"Drum Sampler"},
    {id:"synth", group:"Programm", name:"Synth", osc:"saw"},
    {id:"sampler", group:"Programm", name:"Sampler", osc:"piano"},
    {id:"keys", group:"Programm", name:"Keys", osc:"ep"},
    {id:"organ", group:"Programm", name:"Orgel", osc:"organ"},
    {id:"bass", group:"Programm", name:"Bass", osc:"bass"},
    {id:"lead", group:"Programm", name:"Lead", osc:"lead"},
    {id:"pad", group:"Programm", name:"Pad", osc:"pad"},
    {id:"strings", group:"Programm", name:"Strings", osc:"strings"},
    {id:"brass", group:"Programm", name:"Brass", osc:"brass"},
    {id:"pluck", group:"Programm", name:"Pluck", osc:"pluck"}
  ];
  const DRUMS = [
    {name:"Kick", osc:"bass", n:36},
    {name:"Snare", osc:"pluck", n:50},
    {name:"Hat", osc:"saw", n:82},
    {name:"Tom", osc:"bass", n:45},
    {name:"Clap", osc:"pluck", n:62},
    {name:"Perc", osc:"saw", n:70},
    {name:"Rim", osc:"pluck", n:42},
    {name:"Cym", osc:"saw", n:77}
  ];
  function emptyRack() { return {id:"", on:true, amt:0.65}; }
  let racks = [emptyRack(), emptyRack(), emptyRack(), emptyRack(), emptyRack(), emptyRack(), emptyRack(), emptyRack()];
  let rackNodes = [];
  let rackPick = -1;
  function deviceById(id) { return DEVICES.find((d) => d.id === id) || null; }

  const $ = (id) => document.getElementById(id);
  const chassis = $("chassis");

  let parts = [];
  let selI = 0;
  let assign = "TONE";
  let page = "combi";
  let theme = "rot";
  let patchName = "Italian Grand Presence";
  let bank = {patches:[]};
  let userPatch = null;
  let samples = {};
  let ctx, dry, motion, presence, eqL, eqM, eqH, air, comp, limiter, trim, delay, delayGain, convGain;
  let buses = [], pans = [], analyserL, analyserR, mediaDest, scopeData;
  let started = false, booting = null;
  let voices = [];
  let bend = 0, joyY = 0, expr = 0.9, midiSus = false, midiCh = 0, midiPorts = [], midiAccess = null, midiBoot = null;
  let swLatch = false, spaceDown = false, octDown = false;
  let bpm = 96, delayMul = 0.5;
  let master = {trim:-3, ceil:-0.3, eqL:0.6, eqM:0.3, eqH:1.4, pres:3.1, comp:5.5, room:0.16, dly:0.04, motion:0.12, rate:0.35};
  let lfoPhase = 0, dial = null, persistTimer = 0;
  let recorder = null, recChunks = [], wavProc = null, wavMute = null, wavChunks = [], wavSamples = 0, recStart = 0, recTimer = 0, recLive = false, lastTake = null;
  let bgOn = false, wakeLock = null, keeper = null;
  const ptrNote = new Map();

  function blank(on) {
    return {on, osc:on?"piano":"pad", lo:on?21:36, hi:108, trans:0, level:on?0.9:0, pan:0, cut:5200, res:1.1, atk:0.01, dec:0.4, sus:0.7, rel:0.45};
  }
  function norm(p) {
    const fallback = blank(false);
    const n = Object.assign({}, fallback, p || {}, {on: !!(p && p.on)});
    if (!OSCS.includes(n.osc)) n.osc = "piano";
    ["lo","hi","trans","level","pan","cut","res","atk","dec","sus","rel"].forEach((k) => {
      const v = Number(n[k]);
      n[k] = Number.isFinite(v) ? v : fallback[k];
    });
    n.lo = clamp(Math.round(n.lo), 0, 127);
    n.hi = clamp(Math.round(n.hi), 0, 127);
    n.trans = clamp(Math.round(n.trans), -24, 24);
    if (n.hi < n.lo) n.hi = n.lo;
    return n;
  }
  function holdOn() { return swLatch || spaceDown || midiSus; }
  function noteName(n) { return NAMES[n%12] + (Math.floor(n/12)-1); }
  function midiHz(n) { return 440 * Math.pow(2, (n-69)/12); }
  function clamp(v, a, b) { return Math.min(b, Math.max(a, v)); }
  function status(t) { $("status").textContent = t; }

  function specs() {
    const p = () => parts[selI] || blank(true);
    const num = (label, min, max, get, set) => ({label, min, max, get, set});
    return {
      TONE: [
        num("CUT", 180, 12000, () => p().cut, (v) => setCut(selI, v)),
        num("RES", 0.2, 16, () => p().res, (v) => { p().res = v; }),
        num("ATK", 0.002, 1.8, () => p().atk, (v) => { p().atk = v; }),
        num("DEC", 0.02, 2.4, () => p().dec, (v) => { p().dec = v; }),
        num("SUS", 0, 1, () => p().sus, (v) => { p().sus = v; }),
        num("REL", 0.02, 4, () => p().rel, (v) => { p().rel = v; }),
        num("PAN", -1, 1, () => p().pan, (v) => setPan(selI, v)),
        num("TRS", -24, 24, () => p().trans, (v) => { p().trans = Math.round(v); })
      ],
      MIX: [0,1,2,3].flatMap((i) => [
        num("L"+(i+1), 0, 1.2, () => parts[i].level, (v) => setLevel(i, v)),
        num("P"+(i+1), -1, 1, () => parts[i].pan, (v) => setPan(i, v))
      ]),
      FX: [
        num("PRE", -6, 9, () => master.pres, (v) => { master.pres = v; applyMaster(); }),
        num("ROOM", 0, 0.55, () => master.room, (v) => { master.room = v; applyMaster(); }),
        num("DLY", 0, 0.45, () => master.dly, (v) => { master.dly = v; applyMaster(); }),
        num("LOW", -12, 12, () => master.eqL, (v) => { master.eqL = v; applyMaster(); }),
        num("MID", -12, 12, () => master.eqM, (v) => { master.eqM = v; applyMaster(); }),
        num("AIR", -8, 8, () => master.eqH, (v) => { master.eqH = v; applyMaster(); }),
        num("CMP", 0, 18, () => master.comp, (v) => { master.comp = v; applyMaster(); }),
        num("MOT", 0, 1, () => master.motion, (v) => { master.motion = v; })
      ],
      DYN: [
        num("TRIM", -18, 6, () => master.trim, (v) => { master.trim = v; applyMaster(); paintVol(); }),
        num("CEIL", -3, -0.1, () => master.ceil, (v) => { master.ceil = v; applyMaster(); }),
        num("CMP", 0, 18, () => master.comp, (v) => { master.comp = v; applyMaster(); }),
        num("RATE", 0.05, 1, () => master.rate, (v) => { master.rate = v; }),
        num("PRE", -6, 9, () => master.pres, (v) => { master.pres = v; applyMaster(); }),
        num("ROOM", 0, 0.55, () => master.room, (v) => { master.room = v; applyMaster(); }),
        num("DLY", 0, 0.45, () => master.dly, (v) => { master.dly = v; applyMaster(); }),
        num("LOW", -12, 12, () => master.eqL, (v) => { master.eqL = v; applyMaster(); })
      ]
    };
  }
  function faderSpecs() {
    const spec = (label, min, max, get, set) => ({label, min, max, get, set});
    return [
      spec("P1", 0, 1.2, () => parts[0].level, (v) => setLevel(0, v)),
      spec("P2", 0, 1.2, () => parts[1].level, (v) => setLevel(1, v)),
      spec("P3", 0, 1.2, () => parts[2].level, (v) => setLevel(2, v)),
      spec("P4", 0, 1.2, () => parts[3].level, (v) => setLevel(3, v)),
      spec("MOT", 0, 1, () => master.motion, (v) => { master.motion = v; }),
      spec("PRE", -6, 9, () => master.pres, (v) => { master.pres = v; applyMaster(); }),
      spec("ROOM", 0, 0.55, () => master.room, (v) => { master.room = v; applyMaster(); }),
      spec("DLY", 0, 0.45, () => master.dly, (v) => { master.dly = v; applyMaster(); }),
      spec("MST", -18, 6, () => master.trim, (v) => { master.trim = v; applyMaster(); paintVol(); })
    ];
  }

  function setLevel(i, v) { parts[i].level = v; pushBus(i); schedulePersist(); }
  function setPan(i, v) {
    parts[i].pan = clamp(v, -1, 1);
    if (pans[i] && ctx) pans[i].pan.setTargetAtTime(parts[i].pan, ctx.currentTime, 0.02);
    schedulePersist();
  }
  function setCut(i, v) {
    parts[i].cut = v;
    if (!ctx) return;
    const now = ctx.currentTime;
    voices.forEach((vo) => {
      if (vo.i === i && !vo.dead) vo.filt.frequency.setTargetAtTime(Math.max(40, v), now, 0.03);
    });
  }
  function pushBus(i) {
    if (!buses[i] || !ctx) return;
    const g = parts[i].on ? parts[i].level : 0;
    buses[i].gain.setTargetAtTime(Math.max(0.0001, g), ctx.currentTime, 0.015);
  }
  function applyMaster() {
    if (!started) return;
    trim.gain.setTargetAtTime(Math.pow(10, master.trim/20), ctx.currentTime, 0.02);
    presence.gain.setTargetAtTime(master.pres, ctx.currentTime, 0.02);
    eqL.gain.setTargetAtTime(master.eqL, ctx.currentTime, 0.02);
    eqM.gain.setTargetAtTime(master.eqM, ctx.currentTime, 0.02);
    eqH.gain.setTargetAtTime(master.eqH, ctx.currentTime, 0.02);
    convGain.gain.setTargetAtTime(master.room, ctx.currentTime, 0.02);
    delayGain.gain.setTargetAtTime(master.dly, ctx.currentTime, 0.02);
    const amt = master.comp;
    comp.threshold.setTargetAtTime(-8 - amt*0.7, ctx.currentTime, 0.02);
    comp.ratio.setTargetAtTime(2 + amt*0.25, ctx.currentTime, 0.02);
    limiter.threshold.setTargetAtTime(master.ceil, ctx.currentTime, 0.02);
    const beat = 60 / bpm;
    delay.delayTime.setTargetAtTime(Math.max(0.02, beat * delayMul), ctx.currentTime, 0.03);
    $("tempoRead").textContent = String(bpm);
  }
  function paintJoy() {
    const dot = $("joyDot");
    if (!dot) return;
    dot.style.left = (50 + clamp(bend / 2, -1, 1) * 36) + "%";
    dot.style.top = (50 - clamp(joyY, -1, 1) * 36) + "%";
  }
  function paintRibbon() {
    const cap = $("ribbonCap");
    if (!cap) return;
    cap.style.left = (clamp((expr - 0.4) / 0.75, 0, 1) * 100) + "%";
  }
  function applyBend() {
    if (!ctx) return;
    const now = ctx.currentTime;
    voices.forEach((v) => {
      if (v.dead || !v.rootHz) return;
      const hz = midiHz(v.played) * Math.pow(2, bend/12);
      v.src.playbackRate.setTargetAtTime(hz / v.rootHz, now, 0.02);
    });
  }

  function nearest(fam, hz) {
    const list = samples[fam];
    if (!list || !list.length) return null;
    let best = list[0], d = Math.abs(Math.log(hz/best.hz));
    for (const s of list) {
      const nd = Math.abs(Math.log(hz/s.hz));
      if (nd < d) { d = nd; best = s; }
    }
    return best;
  }
  function makeIR(sec) {
    const n = Math.floor(ctx.sampleRate * sec);
    const b = ctx.createBuffer(2, n, ctx.sampleRate);
    for (let c = 0; c < 2; c++) {
      const d = b.getChannelData(c);
      for (let i = 0; i < n; i++) d[i] = (Math.random()*2-1) * Math.pow(1-i/n, 2.6);
    }
    return b;
  }
  async function boot() {
    ctx = new AudioContext({latencyHint:"interactive"});
    dry = ctx.createGain();
    motion = ctx.createBiquadFilter(); motion.type = "lowpass"; motion.frequency.value = 14000; motion.Q.value = 0.7;
    presence = ctx.createBiquadFilter(); presence.type = "peaking"; presence.frequency.value = 3250; presence.Q.value = 0.85;
    eqL = ctx.createBiquadFilter(); eqL.type = "lowshelf"; eqL.frequency.value = 120;
    eqM = ctx.createBiquadFilter(); eqM.type = "peaking"; eqM.frequency.value = 900; eqM.Q.value = 0.7;
    eqH = ctx.createBiquadFilter(); eqH.type = "highshelf"; eqH.frequency.value = 8000;
    air = ctx.createBiquadFilter(); air.type = "highshelf"; air.frequency.value = 12000; air.gain.value = 1.1;
    comp = ctx.createDynamicsCompressor();
    limiter = ctx.createDynamicsCompressor();
    limiter.knee.value = 0; limiter.ratio.value = 20; limiter.attack.value = 0.002; limiter.release.value = 0.05;
    trim = ctx.createGain();
    delay = ctx.createDelay(1.5); delay.delayTime.value = 0.32;
    const fb = ctx.createGain(); fb.gain.value = 0.28;
    delayGain = ctx.createGain();
    const conv = ctx.createConvolver(); conv.buffer = makeIR(1.6);
    convGain = ctx.createGain();
    mediaDest = ctx.createMediaStreamDestination();
    const split = ctx.createChannelSplitter(2);
    analyserL = ctx.createAnalyser(); analyserR = ctx.createAnalyser();
    analyserL.fftSize = 1024; analyserR.fftSize = 1024;
    scopeData = new Uint8Array(analyserL.fftSize);
    dry.connect(delay); delay.connect(fb); fb.connect(delay); delay.connect(delayGain); delayGain.connect(presence);
    dry.connect(conv); conv.connect(convGain); convGain.connect(presence);
    rackNodes = [];
    let prev = dry;
    for (let i = 0; i < 8; i++) {
      const input = ctx.createGain();
      const thru = ctx.createGain(); thru.gain.value = 1;
      const fxIn = ctx.createGain();
      const wet = ctx.createGain(); wet.gain.value = 0;
      const out = ctx.createGain();
      input.connect(thru); thru.connect(out);
      input.connect(fxIn);
      wet.connect(out);
      prev.connect(input);
      prev = out;
      rackNodes.push({input, thru, fxIn, wet, out, stop:null});
    }
    prev.connect(motion);
    motion.connect(presence); presence.connect(eqL); eqL.connect(eqM); eqM.connect(eqH); eqH.connect(air);
    air.connect(comp); comp.connect(limiter); limiter.connect(trim);
    trim.connect(ctx.destination); trim.connect(mediaDest); trim.connect(split);
    split.connect(analyserL, 0); split.connect(analyserR, 1);
    buses = []; pans = [];
    for (let i = 0; i < 4; i++) {
      const g = ctx.createGain();
      const pan = ctx.createStereoPanner();
      g.connect(pan); pan.connect(dry);
      buses.push(g); pans.push(pan);
    }
    for (const fam of Object.keys(samples)) {
      const ok = [];
      for (const s of samples[fam]) {
        try { s.buf = await ctx.decodeAudioData(s.raw.slice(0)); ok.push(s); } catch (_) {}
      }
      samples[fam] = ok.sort((a,b) => a.hz - b.hz);
    }
    started = true;
    parts.forEach((_, i) => { pushBus(i); setPan(i, parts[i].pan); });
    applyMaster();
    applyRacks();
    if (bgOn) await setBg(true, true);
    status(ctx.sampleRate + " Hz · Beta 1.0 · " + Object.keys(samples).length + " Bänke · Ceiling " + master.ceil.toFixed(1));
  }
  function ensure() {
    if (started) return ctx.state === "suspended" ? ctx.resume() : Promise.resolve();
    if (!booting) booting = boot().catch((err) => { booting = null; status(err.message || "Audio blockiert"); throw err; });
    return booting;
  }

  function steal() {
    const live = voices.filter((v) => !v.dead);
    if (live.length < POLY) return;
    live.sort((a,b) => a.t - b.t);
    release(live[0], true);
  }
  function spawn(fam, midi, vel, bus) {
    if (!started) return;
    const played = midi;
    const hz = midiHz(played) * Math.pow(2, bend/12);
    const root = nearest(fam, hz);
    if (!root || !root.buf) return;
    steal();
    const src = ctx.createBufferSource();
    src.buffer = root.buf;
    src.playbackRate.value = hz / root.hz;
    const filt = ctx.createBiquadFilter();
    filt.type = "lowpass";
    const g = ctx.createGain();
    src.connect(filt); filt.connect(g); g.connect(bus || dry);
    const t = ctx.currentTime;
    const peak = Math.max(0.001, vel * expr);
    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(peak, t + 0.01);
    src.start();
    const voice = {t, midi, played, src, g, filt, rel:0.3, dead:false, held:false, pad:false, rootHz:root.hz, i:-1};
    voices.push(voice);
    return voice;
  }
  function startPart(i, midi, vel) {
    const p = parts[i];
    if (!p || !p.on) return;
    const n = clamp(midi + (p.trans|0) + (octDown ? -12 : 0), 0, 127);
    if (n < p.lo || n > p.hi) return;
    const v = spawn(p.osc, n, vel * 0.95, buses[i]);
    if (!v) return;
    v.i = i;
    v.midi = midi;
    v.rel = p.rel;
    v.filt.Q.value = p.res;
    const bright = p.cut * (0.45 + vel*0.7);
    const t = ctx.currentTime;
    v.filt.frequency.setValueAtTime(Math.max(80, bright*0.45), t);
    v.filt.frequency.exponentialRampToValueAtTime(Math.max(90, bright), t + Math.max(0.02, p.atk));
    const peak = Math.max(0.001, vel * expr);
    v.g.gain.cancelScheduledValues(t);
    v.g.gain.setValueAtTime(0.0001, t);
    v.g.gain.exponentialRampToValueAtTime(peak, t + Math.max(0.003, p.atk));
    v.g.gain.exponentialRampToValueAtTime(Math.max(0.0002, peak*p.sus), t + p.atk + p.dec);
  }
  function noteOn(midi, vel) {
    if (!started) return;
    voices.forEach((v) => { if (!v.pad && v.midi === midi && !v.dead) release(v, true); });
    parts.forEach((_, i) => startPart(i, midi, vel == null ? 0.86 : vel));
    const el = document.querySelector('.key[data-midi="'+midi+'"]');
    if (el) el.classList.add("on");
  }
  function release(v, fast) {
    if (!v || v.dead || !ctx) return;
    v.dead = true;
    const t = ctx.currentTime;
    const r = fast ? 0.04 : Math.max(0.03, v.rel);
    try {
      v.g.gain.cancelScheduledValues(t);
      v.g.gain.setValueAtTime(Math.max(0.0001, v.g.gain.value), t);
      v.g.gain.exponentialRampToValueAtTime(0.0001, t + r);
    } catch (_) {}
    setTimeout(() => {
      try { v.src.stop(); } catch (_) {}
      try { v.src.disconnect(); v.filt.disconnect(); v.g.disconnect(); } catch (_) {}
      if (voices.length > 40) voices = voices.filter((x) => !x.dead);
    }, r*1000 + 40);
  }
  function noteOff(midi) {
    const el = document.querySelector('.key[data-midi="'+midi+'"]');
    if (el) el.classList.remove("on");
    voices.forEach((v) => {
      if (v.pad || v.midi !== midi || v.dead) return;
      if (holdOn()) v.held = true;
      else release(v);
    });
  }
  function panic() {
    voices.forEach((v) => release(v, true));
    document.querySelectorAll(".key.on").forEach((el) => el.classList.remove("on"));
  }
  function liftHold() {
    if (holdOn()) return;
    voices.forEach((v) => { if (v.held) release(v); });
  }

  function padVoice(osc) {
    return {on:true, osc, lo:0, hi:127, trans:0, level:1, pan:0, cut:6400, res:0.8, atk:0.004, dec:0.22, sus:0.35, rel:0.28};
  }
  function hitPad(i) {
    const drum = racks.some((r) => r.id === "drums" && r.on);
    const p = (drum ? DRUMS : PADS)[i];
    if (!p || !started) return;
    const tmp = padVoice(p.osc);
    const voice = spawn(tmp.osc, p.n, 0.92, dry);
    if (!voice) return;
    voice.pad = true;
    voice.rel = 0.28;
    voice.filt.frequency.setTargetAtTime(tmp.cut, ctx.currentTime, 0.01);
    const t = ctx.currentTime;
    voice.g.gain.setValueAtTime(0.0001, t);
    voice.g.gain.exponentialRampToValueAtTime(0.9, t+0.008);
    voice.g.gain.exponentialRampToValueAtTime(0.25, t+0.18);
    setTimeout(() => release(voice), 420);
  }

  function snapshot() {
    return {
      version:"1.0.0-beta", id:"rn-"+Date.now(), name: patchName, theme, parts: parts.map((p) => Object.assign({}, p)),
      master: Object.assign({}, master), bpm, delayMul, page, assign, selI,
      racks: racks.map((r) => ({id:r.id, on:!!r.on, amt:r.amt}))
    };
  }
  function schedulePersist() {
    clearTimeout(persistTimer);
    persistTimer = setTimeout(() => {
      try { localStorage.setItem("rn-sx-session", JSON.stringify(snapshot())); } catch (_) {}
    }, 250);
  }
  function applyPatch(p, store) {
    if (!p) return;
    patchName = p.name || "Patch";
    if (p.theme === "rot" || p.theme === "blau") setTheme(p.theme);
    const src = (p.parts && p.parts.length ? p.parts : [blank(true)]).slice(0, 4).map(norm);
    while (src.length < 4) src.push(blank(false));
    parts = src;
    if (p.master && typeof p.master === "object") {
      Object.keys(master).forEach((k) => {
        const v = Number(p.master[k]);
        if (Number.isFinite(v)) master[k] = v;
      });
    }
    master.ceil = clamp(master.ceil, -3, -0.1);
    if (Number.isFinite(Number(p.bpm))) bpm = clamp(Math.round(Number(p.bpm)), 40, 240);
    if (Array.isArray(p.racks)) {
      racks = p.racks.slice(0, 8).map((r) => ({
        id: deviceById(r && r.id) ? r.id : "",
        on: !r || r.on !== false,
        amt: Number.isFinite(Number(r && r.amt)) ? clamp(Number(r.amt), 0, 1) : 0.65
      }));
      while (racks.length < 8) racks.push(emptyRack());
    }
    selI = Math.max(0, parts.findIndex((x) => x.on));
    $("patchTitle").textContent = patchName;
    if (started) {
      parts.forEach((_, i) => { pushBus(i); setPan(i, parts[i].pan); });
      applyMaster();
      applyRacks();
    }
    paintAll();
    renderPage();
    if (store !== false) schedulePersist();
    if (navigator.mediaSession && navigator.mediaSession.metadata !== undefined) {
      try {
        navigator.mediaSession.metadata = new MediaMetadata({title: patchName, artist:"RICH NEON SX", album:"Beta Final 1.0"});
      } catch (_) {}
    }
  }

  function tOf(v, min, max) { return (clamp(v, min, max) - min) / (max - min || 1); }
  function paintKnob(el, t) {
    const i = el.querySelector("i");
    if (i) i.style.transform = "rotate(" + (-140 + t*280) + "deg)";
  }
  function paintAll() {
    const list = specs()[assign] || [];
    document.querySelectorAll("#knobs .knob").forEach((el, i) => {
      const s = list[i];
      if (!s) return;
      el.querySelector("span").textContent = s.label;
      paintKnob(el, tOf(s.get(), s.min, s.max));
    });
    const fs = faderSpecs();
    document.querySelectorAll("#faders .fader").forEach((el, i) => {
      const s = fs[i];
      el.querySelector("span").textContent = s.label;
      const t = tOf(s.get(), s.min, s.max);
      el.querySelector(".track i").style.bottom = "calc(" + (t*100) + "% - 7px)";
    });
    paintVol();
    document.querySelectorAll("#assign button").forEach((b) => b.classList.toggle("on", b.dataset.assign === assign));
    document.querySelectorAll(".modes button").forEach((b) => b.classList.toggle("on", b.dataset.page === page));
    document.querySelectorAll("#banks button").forEach((b) => {
      const i = +b.dataset.bank;
      const src = i === 7 ? (userPatch || (bank.patches||[])[7]) : (bank.patches||[])[i];
      b.classList.toggle("on", !!(src && src.name === patchName));
    });
  }
  function paintVol() {
    const t = tOf(master.trim, -18, 6);
    $("volCap").style.transform = "rotate(" + (-140 + t*280) + "deg)";
  }
  function armDial(spec) { dial = spec; }

  function renderPage() {
    const root = $("page");
    root.innerHTML = "";
    $("lcdTitle").textContent = page.toUpperCase();
    if (page === "combi") renderCombi(root);
    else if (page === "prog") renderProg(root);
    else if (page === "seq") renderSeq(root);
    else if (page === "samp") renderSamp(root);
    else if (page === "global") renderGlobal(root);
    else if (page === "media") renderMedia(root);
    else if (page === "rack") renderRack(root);
    else renderSet(root);
  }
  function renderCombi(root) {
    const name = document.createElement("input");
    name.type = "text";
    name.value = patchName;
    name.id = "patchName";
    root.appendChild(name);
    parts.forEach((p, i) => {
      const row = document.createElement("div");
      row.className = "rowp" + (i === selI ? " on" : "");
      row.dataset.sel = String(i);
      const ck = document.createElement("input");
      ck.type = "checkbox"; ck.checked = p.on; ck.dataset.part = String(i); ck.dataset.field = "on";
      const lab = document.createElement("b"); lab.textContent = "P"+(i+1);
      const sel = document.createElement("select");
      sel.dataset.part = String(i); sel.dataset.field = "osc";
      OSCS.forEach((o) => {
        const op = document.createElement("option");
        op.value = o; op.textContent = o; if (o === p.osc) op.selected = true;
        sel.appendChild(op);
      });
      const lo = numInput(p.lo, i, "lo");
      const hi = numInput(p.hi, i, "hi");
      row.append(ck, lab, sel, lo, hi);
      root.appendChild(row);
    });
    const hint = document.createElement("p");
    hint.className = "hint";
    hint.textContent = "Vier Lagen, Split über die Tastatur. Regler gelten für die markierte Part. Master sitzt hinter dem Limiter, Ceiling " + master.ceil.toFixed(1) + " dBTP.";
    root.appendChild(hint);
  }
  function numInput(v, i, field) {
    const n = document.createElement("input");
    n.type = "number"; n.value = String(v);
    n.dataset.part = String(i); n.dataset.field = field;
    return n;
  }
  function renderProg(root) {
    const grid = document.createElement("div");
    grid.className = "prog";
    OSCS.forEach((o) => {
      const b = document.createElement("button");
      b.type = "button"; b.textContent = o;
      b.dataset.osc = o;
      if (parts[selI] && parts[selI].osc === o) b.className = "on";
      grid.appendChild(b);
    });
    root.appendChild(grid);
    const hint = document.createElement("p");
    hint.className = "hint";
    hint.textContent = "Programm der Part P" + (selI+1) + ". Eigene Multisamples, nächste Root-Note, keine Fremd-ROMs.";
    root.appendChild(hint);
  }
  function renderSeq(root) {
    const hint = document.createElement("p");
    hint.className = "hint";
    hint.textContent = "REC nimmt den Master auf. STOP schreibt eine WAV, 16 bit, volle Samplerate, ohne Extra-Pegel. Bis 10 Minuten WAV, danach WebM bis 2,2 Stunden. EXPORT holt die letzte Datei noch einmal.";
    const sel = document.createElement("select");
    sel.id = "divSel";
    [["1/4", 1], ["1/8", 0.5], ["1/8.", 0.75], ["1/16", 0.25]].forEach(([lab, v]) => {
      const op = document.createElement("option");
      op.value = String(v); op.textContent = "Delay " + lab;
      if (Math.abs(delayMul - v) < 0.01) op.selected = true;
      sel.appendChild(op);
    });
    root.append(hint, sel);
  }
  function renderSamp(root) {
    const hint = document.createElement("p");
    hint.className = "hint";
    const fams = Object.keys(samples);
    hint.textContent = fams.length
      ? fams.map((f) => f + " " + samples[f].length).join(" · ")
      : "Bank wird geladen.";
    root.appendChild(hint);
  }
  function renderGlobal(root) {
    const hint = document.createElement("p");
    hint.className = "hint";
    hint.textContent = "Hintergrund hält die Engine, wenn das Display ausgeht oder die App liegt. Auf Android als laufende Wiedergabe.";
    const ceil = document.createElement("input");
    ceil.type = "range"; ceil.min = "-3"; ceil.max = "-0.1"; ceil.step = "0.1"; ceil.value = String(master.ceil); ceil.id = "ceilRange";
    const row = document.createElement("div");
    row.className = "midi-row";
    const dot = document.createElement("i");
    dot.id = "midiDot";
    const live = document.createElement("b");
    live.id = "midiLive";
    live.textContent = "MIDI";
    const sel = document.createElement("select");
    sel.id = "midiCh";
    const omni = document.createElement("option");
    omni.value = "0"; omni.textContent = "OMNI";
    sel.appendChild(omni);
    for (let c = 1; c <= 16; c++) {
      const op = document.createElement("option");
      op.value = String(c); op.textContent = "Kanal " + c;
      sel.appendChild(op);
    }
    sel.value = String(midiCh);
    const devs = document.createElement("p");
    devs.id = "midiDevs"; devs.className = "hint";
    const map = document.createElement("p");
    map.className = "hint";
    map.textContent = "USB: Akai LPK, MPK Mini bis MPK261, MPD, LPD, APC. Pads Kanal 10. Traktor nur im MIDI-Modus. MPC Studio Black sendet kein USB-MIDI. Chinch ist Audio über LINE.";
    row.append(dot, live, sel);
    root.append(hint, ceil, row, devs, map);
    paintMidiPorts();
  }
  function renderMedia(root) {
    const box = document.createElement("div");
    box.className = "media-actions grid2";
    const a = document.createElement("a");
    a.className = "apk big-apk";
    if (window.Android) a.textContent = "BEREITS INSTALLIERT";
    else { a.textContent = "APK LADEN"; a.href = "/RICH-NEON-2026.apk"; a.download = "RICH-NEON-2026.apk"; }
    const save = document.createElement("button");
    save.type = "button"; save.dataset.act = "save"; save.textContent = "PATCH SPEICHERN";
    const load = document.createElement("button");
    load.type = "button"; load.dataset.act = "load"; load.textContent = "JSON LADEN";
    const exp = document.createElement("button");
    exp.type = "button"; exp.dataset.act = "export"; exp.textContent = "AUDIO EXPORT";
    box.append(a, exp, save, load);
    root.appendChild(box);
  }
  function renderSet(root) {
    const box = document.createElement("div");
    box.className = "setlist";
    (bank.patches||[]).forEach((p) => {
      const b = document.createElement("button");
      b.type = "button"; b.textContent = p.name; b.dataset.patch = p.id;
      if (p.name === patchName) b.className = "on";
      box.appendChild(b);
    });
    if (userPatch) {
      const b = document.createElement("button");
      b.type = "button"; b.textContent = "User · " + (userPatch.name || "Patch"); b.dataset.act = "user";
      box.appendChild(b);
    }
    root.appendChild(box);
  }

  function renderRack(root) {
    const hint = document.createElement("p");
    hint.className = "hint";
    hint.textContent = "Acht leere Racks. Effekt liegt im Master. Drum-Sampler übernimmt die Pads. Programm setzt die gewählte Part.";
    root.appendChild(hint);
    const box = document.createElement("div");
    box.className = "rack";
    racks.forEach((slot, i) => {
      const row = document.createElement("div");
      row.className = "slotrow";
      const n = document.createElement("b");
      n.textContent = String(i + 1);
      const open = document.createElement("button");
      open.type = "button";
      open.dataset.act = "rack";
      open.dataset.slot = String(i);
      const dev = deviceById(slot.id);
      open.textContent = dev ? dev.group + " · " + dev.name : "LEER";
      if (dev && slot.on) open.className = "on";
      const amt = document.createElement("input");
      amt.type = "range"; amt.min = "0"; amt.max = "1"; amt.step = "0.01"; amt.value = String(slot.amt);
      amt.dataset.rackamt = String(i);
      amt.disabled = !dev;
      const clear = document.createElement("button");
      clear.type = "button"; clear.dataset.act = "rack-x"; clear.dataset.slot = String(i); clear.textContent = "×";
      row.append(n, open, amt, clear);
      box.appendChild(row);
      if (rackPick === i) {
        const pick = document.createElement("div");
        pick.className = "rackpick";
        let group = "";
        DEVICES.forEach((d) => {
          if (d.group !== group) {
            group = d.group;
            const h = document.createElement("b");
            h.textContent = group.toUpperCase();
            pick.appendChild(h);
          }
          const b = document.createElement("button");
          b.type = "button";
          b.dataset.dev = d.id;
          b.dataset.slot = String(i);
          b.textContent = d.name;
          pick.appendChild(b);
        });
        const bypass = document.createElement("button");
        bypass.type = "button";
        bypass.dataset.act = "rack-by";
        bypass.dataset.slot = String(i);
        bypass.textContent = slot.on ? "AN" : "BYPASS";
        pick.appendChild(bypass);
        box.appendChild(pick);
      }
    });
    root.appendChild(box);
  }
  function buildEffect(id, amt) {
    const t = clamp(amt, 0, 1);
    if (id === "eq") {
      const f = ctx.createBiquadFilter();
      f.type = "peaking"; f.frequency.value = 1400; f.Q.value = 0.8; f.gain.value = (t * 2 - 1) * 12;
      return {start:f, end:f, series:true};
    }
    if (id === "comp") {
      const c = ctx.createDynamicsCompressor();
      c.threshold.value = -8 - t * 20; c.ratio.value = 1.4 + t * 6; c.attack.value = 0.012; c.release.value = 0.18;
      return {start:c, end:c, series:true};
    }
    if (id === "filter") {
      const f = ctx.createBiquadFilter();
      f.type = "lowpass"; f.frequency.value = 180 + Math.pow(t, 2) * 14000; f.Q.value = 0.8;
      return {start:f, end:f, series:true};
    }
    if (id === "delay") {
      const d = ctx.createDelay(1.2); d.delayTime.value = 0.26;
      const fbG = ctx.createGain(); fbG.gain.value = 0.2 + t * 0.35;
      const g = ctx.createGain(); g.gain.value = 0.15 + t * 0.55;
      d.connect(fbG); fbG.connect(d); d.connect(g);
      return {start:d, end:g, series:false};
    }
    if (id === "hall") {
      const c = ctx.createConvolver(); c.buffer = makeIR(0.8 + t * 1.4);
      const g = ctx.createGain(); g.gain.value = 0.12 + t * 0.55;
      c.connect(g);
      return {start:c, end:g, series:false};
    }
    if (id === "chorus") {
      const d = ctx.createDelay(0.05); d.delayTime.value = 0.014;
      const g = ctx.createGain(); g.gain.value = 0.25 + t * 0.45;
      const lfo = ctx.createOscillator();
      const lg = ctx.createGain(); lg.gain.value = 0.003 + t * 0.004;
      lfo.frequency.value = 0.35 + t * 2.2;
      lfo.connect(lg); lg.connect(d.delayTime); d.connect(g); lfo.start();
      return {start:d, end:g, series:false, stop:() => { try { lfo.stop(); } catch (_) {} }};
    }
    if (id === "drive") {
      const sh = ctx.createWaveShaper();
      const curve = new Float32Array(256);
      const k = 1 + t * 28;
      for (let i = 0; i < 256; i++) {
        const x = (i / 255) * 2 - 1;
        curve[i] = Math.tanh(x * k);
      }
      sh.curve = curve;
      const g = ctx.createGain(); g.gain.value = 0.55;
      sh.connect(g);
      return {start:sh, end:g, series:true};
    }
    const c = ctx.createDynamicsCompressor();
    c.threshold.value = -1 - t * 10; c.knee.value = 0; c.ratio.value = 20; c.attack.value = 0.002; c.release.value = 0.05;
    return {start:c, end:c, series:true};
  }
  function wireSlot(i) {
    const s = rackNodes[i];
    if (!s || !ctx) return;
    if (s.stop) { try { s.stop(); } catch (_) {} s.stop = null; }
    if (s.end) { try { s.end.disconnect(); } catch (_) {} s.end = null; }
    try { s.fxIn.disconnect(); } catch (_) {}
    const spec = racks[i];
    const dev = deviceById(spec.id);
    const fx = !!(dev && dev.group === "Effekt" && spec.on);
    if (!fx) {
      s.thru.gain.setTargetAtTime(1, ctx.currentTime, 0.02);
      s.wet.gain.setTargetAtTime(0, ctx.currentTime, 0.02);
      return;
    }
    const built = buildEffect(spec.id, spec.amt);
    s.stop = built.stop || null;
    s.fxIn.connect(built.start);
    built.end.connect(s.wet);
    s.end = built.end;
    s.thru.gain.setTargetAtTime(built.series ? 0 : 1, ctx.currentTime, 0.02);
    s.wet.gain.setTargetAtTime(1, ctx.currentTime, 0.02);
  }
  function applyRacks() {
    if (!started) return;
    for (let i = 0; i < rackNodes.length; i++) wireSlot(i);
  }

  function setTheme(name) {
    theme = name;
    chassis.dataset.theme = name;
    $("btnRot").classList.toggle("on", name === "rot");
    $("btnBlau").classList.toggle("on", name === "blau");
  }
  async function setBg(on, quiet) {
    bgOn = on;
    $("btnBg").classList.toggle("on", on);
    try { localStorage.setItem("rn-sx-bg", on ? "1" : "0"); } catch (_) {}
    if (window.Android && Android.setBackground) Android.setBackground(!!on);
    if (on && navigator.wakeLock) {
      try { wakeLock = await navigator.wakeLock.request("screen"); } catch (_) {}
    } else if (wakeLock) {
      try { await wakeLock.release(); } catch (_) {}
      wakeLock = null;
    }
    if (started) {
      if (on && !keeper) {
        const o = ctx.createOscillator();
        const g = ctx.createGain();
        o.frequency.value = 28; g.gain.value = 0.00002;
        o.connect(g); g.connect(ctx.destination); o.start();
        keeper = o;
      } else if (!on && keeper) {
        try { keeper.stop(); } catch (_) {}
        keeper = null;
      }
    }
    if (navigator.mediaSession) {
      try {
        navigator.mediaSession.playbackState = on ? "playing" : "paused";
        navigator.mediaSession.metadata = new MediaMetadata({title: patchName, artist:"RICH NEON SX", album:"Beta Final 1.0"});
      } catch (_) {}
    }
    if (!quiet) status(on ? "Hintergrund an · Audio bleibt aktiv" : "Hintergrund aus");
  }

  function download(blob, name) {
    if (window.Android && Android.beginSave) {
      Android.beginSave(name, blob.type || "application/octet-stream");
      const reader = blob.stream().getReader();
      const step = 0x6000;
      const pump = () => reader.read().then(({done, value}) => {
        if (done) { Android.endSave(); return; }
        for (let i = 0; i < value.length; i += step) {
          const slice = value.subarray(i, Math.min(value.length, i+step));
          let s = "";
          for (let k = 0; k < slice.length; k++) s += String.fromCharCode(slice[k]);
          Android.appendB64(btoa(s));
        }
        return pump();
      }).catch((err) => { try { Android.cancelSave(String(err)); } catch (_) {} });
      pump();
      return;
    }
    const a = document.createElement("a");
    a.href = URL.createObjectURL(blob);
    a.download = name;
    document.body.appendChild(a);
    a.click();
    setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 1500);
  }
  function wavHeader(frames, sr) {
    const dataBytes = frames * 4;
    const b = new ArrayBuffer(44 + dataBytes);
    const v = new DataView(b);
    const w = (o, s) => { for (let i = 0; i < s.length; i++) v.setUint8(o+i, s.charCodeAt(i)); };
    w(0, "RIFF"); v.setUint32(4, 36+dataBytes, true); w(8, "WAVE"); w(12, "fmt ");
    v.setUint32(16, 16, true); v.setUint16(20, 1, true); v.setUint16(22, 2, true);
    v.setUint32(24, sr, true); v.setUint32(28, sr*4, true); v.setUint16(32, 4, true); v.setUint16(34, 16, true);
    w(36, "data"); v.setUint32(40, dataBytes, true);
    return v;
  }
  async function startRec() {
    if (recLive) return;
    if (!started) await ensure();
    if (!started) return;
    recLive = true;
    recChunks = []; wavChunks = []; wavSamples = 0;
    recorder = null;
    const mimes = ["audio/webm;codecs=opus", "audio/webm", "audio/mp4"];
    if (window.MediaRecorder) {
      for (const mime of mimes) {
        try {
          if (MediaRecorder.isTypeSupported && !MediaRecorder.isTypeSupported(mime)) continue;
          recorder = new MediaRecorder(mediaDest.stream, {mimeType:mime, audioBitsPerSecond:192000});
          break;
        } catch (_) {}
      }
    }
    if (recorder) {
      recorder.ondataavailable = (e) => { if (e.data && e.data.size) recChunks.push(e.data); };
      recorder.onerror = () => { recorder = null; };
      recorder.onstop = flushRec;
      recorder.start(250);
    }
    try {
      const rec = ctx.createScriptProcessor(4096, 2, 2);
      wavMute = ctx.createGain(); wavMute.gain.value = 0;
      wavProc = rec;
      rec.onaudioprocess = (e) => {
        if (!recLive || (wavSamples / ctx.sampleRate) >= WAV_MAX) return;
        const l = e.inputBuffer.getChannelData(0);
        const r = e.inputBuffer.numberOfChannels > 1 ? e.inputBuffer.getChannelData(1) : l;
        const out = new Int16Array(l.length * 2);
        for (let i = 0; i < l.length; i++) {
          out[i*2] = clamp(l[i]*32767, -32768, 32767);
          out[i*2+1] = clamp(r[i]*32767, -32768, 32767);
        }
        wavChunks.push(out);
        wavSamples += l.length;
      };
      trim.connect(rec); rec.connect(wavMute); wavMute.connect(ctx.destination);
    } catch (_) { wavProc = null; wavMute = null; }
    recStart = performance.now();
    $("btnRec").classList.add("on");
    clearInterval(recTimer);
    recTimer = setInterval(() => {
      const sec = (performance.now() - recStart) / 1000;
      const h = Math.floor(sec/3600), m = Math.floor(sec/60)%60, s = Math.floor(sec)%60;
      $("recTime").textContent = [h,m,s].map((n) => String(n).padStart(2,"0")).join(":");
      if (sec >= MAX_SEC) stopRec();
    }, 200);
    status("Aufnahme · Master");
  }
  function stopRec() {
    if (!recLive) return;
    recLive = false;
    const had = recorder && recorder.state === "recording";
    if (had) {
      try { recorder.requestData(); } catch (_) {}
      try { recorder.stop(); } catch (_) { flushRec(); }
    }
    if (wavProc) { try { wavProc.disconnect(); } catch (_) {} wavProc.onaudioprocess = null; wavProc = null; }
    if (wavMute) { try { wavMute.disconnect(); } catch (_) {} wavMute = null; }
    clearInterval(recTimer);
    $("btnRec").classList.remove("on");
    if (!had) flushRec();
  }
  function takeName(ext) {
    const stamp = new Date().toISOString().replace(/[:.]/g, "-").slice(0, 19);
    const stem = String(patchName || "rich-neon").replace(/[^A-Za-z0-9]+/g, "-").replace(/^-|-$/g, "").slice(0, 40) || "rich-neon";
    return stem + "-" + stamp + ext;
  }
  function flushRec() {
    const sr = ctx ? ctx.sampleRate : 44100;
    const dur = wavSamples / sr;
    const long = dur >= WAV_MAX - 0.25;
    let blob = null, name = "", kind = "";
    if (!long && wavChunks.length && wavSamples > 0) {
      try {
        const view = wavHeader(wavSamples, sr);
        let off = 44;
        wavChunks.forEach((ch) => { new Int16Array(view.buffer, off, ch.length).set(ch); off += ch.byteLength; });
        blob = new Blob([view.buffer], {type:"audio/wav"});
        name = takeName(".wav");
        kind = "WAV 16-bit · " + (sr / 1000).toFixed(1) + " kHz · 100%";
      } catch (_) { blob = null; }
    }
    if (!blob && recChunks.length) {
      blob = new Blob(recChunks, {type:(recorder && recorder.mimeType) || "audio/webm"});
      name = takeName(".webm");
      kind = long ? "WebM · über 10 min" : "WebM";
    }
    recChunks = []; wavChunks = []; wavSamples = 0;
    if (!blob) { status("nichts aufgenommen"); return; }
    lastTake = {blob, name, kind};
    download(blob, name);
    status("Export · " + kind);
  }
  function askExport() {
    if (recLive) { stopRec(); return; }
    if (!lastTake) { status("Erst REC, dann Export"); return; }
    download(lastTake.blob, lastTake.name);
    status("Export · " + lastTake.kind);
  }

  function buildControls() {
    const knobs = $("knobs");
    for (let i = 0; i < 8; i++) {
      const el = document.createElement("div");
      el.className = "knob";
      el.innerHTML = "<b><i></i></b><span>—</span>";
      bindRel(el, (dy) => {
        const s = specs()[assign][i];
        const span = s.max - s.min;
        const v = clamp(s.get() + dy / 150 * span, s.min, s.max);
        s.set(v); armDial(s); paintAll();
      });
      knobs.appendChild(el);
    }
    const faders = $("faders");
    faderSpecs().forEach((s, i) => {
      const el = document.createElement("div");
      el.className = "fader";
      el.innerHTML = '<div class="track"><i></i></div><span></span>';
      bindAbs(el, (t) => {
        const spec = faderSpecs()[i];
        spec.set(spec.min + t * (spec.max - spec.min));
        armDial(spec);
        paintAll();
      });
      faders.appendChild(el);
    });
    bindRel($("vol"), (dy) => {
      master.trim = clamp(master.trim + dy / 8, -18, 6);
      applyMaster(); paintVol(); armDial({get:()=>master.trim, set:(v)=>{master.trim=v; applyMaster(); paintVol();}, min:-18, max:6});
    });
    bindRel($("dial"), (dy) => {
      if (!dial) return;
      const span = dial.max - dial.min;
      dial.set(clamp(dial.get() + dy / 120 * span, dial.min, dial.max));
      paintAll();
    });
    const joy = $("joy");
    const moveJoy = (ev) => {
      const r = joy.getBoundingClientRect();
      const x = clamp((ev.clientX - r.left) / r.width * 2 - 1, -1, 1);
      const y = clamp(1 - (ev.clientY - r.top) / r.height * 2, -1, 1);
      bend = x * 2; joyY = y; applyBend(); paintJoy();
    };
    joy.addEventListener("pointerdown", (ev) => { try { joy.setPointerCapture(ev.pointerId); } catch (_) {} moveJoy(ev); });
    joy.addEventListener("pointermove", (ev) => { if (joy.hasPointerCapture(ev.pointerId)) moveJoy(ev); });
    joy.addEventListener("pointerup", resetJoy);
    joy.addEventListener("pointercancel", resetJoy);
    function resetJoy() {
      bend = 0; joyY = 0; applyBend(); paintJoy();
    }
    const ribbon = $("ribbon");
    const moveRib = (ev) => {
      const r = ribbon.getBoundingClientRect();
      const t = clamp((ev.clientX - r.left) / r.width, 0, 1);
      expr = 0.4 + t * 0.75;
      paintRibbon();
    };
    ribbon.addEventListener("pointerdown", (ev) => { try { ribbon.setPointerCapture(ev.pointerId); } catch (_) {} moveRib(ev); });
    ribbon.addEventListener("pointermove", (ev) => { if (ribbon.hasPointerCapture(ev.pointerId)) moveRib(ev); });
  }
  function bindRel(el, onDy) {
    let last = 0;
    el.addEventListener("pointerdown", (ev) => {
      ev.preventDefault();
      try { el.setPointerCapture(ev.pointerId); } catch (_) {}
      last = ev.clientY;
    });
    el.addEventListener("pointermove", (ev) => {
      if (!el.hasPointerCapture(ev.pointerId)) return;
      onDy(last - ev.clientY);
      last = ev.clientY;
    });
  }
  function bindAbs(el, onT) {
    const apply = (ev) => {
      const r = el.getBoundingClientRect();
      onT(clamp(1 - (ev.clientY - r.top) / r.height, 0, 1));
    };
    el.addEventListener("pointerdown", (ev) => {
      ev.preventDefault();
      try { el.setPointerCapture(ev.pointerId); } catch (_) {}
      apply(ev);
    });
    el.addEventListener("pointermove", (ev) => { if (el.hasPointerCapture(ev.pointerId)) apply(ev); });
  }

  function buildBanks() {
    const box = $("banks");
    box.innerHTML = "";
    const labels = ["A","B","C","D","E","F","G","USR"];
    labels.forEach((lab, i) => {
      const b = document.createElement("button");
      b.type = "button"; b.textContent = lab; b.dataset.bank = String(i);
      box.appendChild(b);
    });
  }
  function buildPads() {
    const box = $("pads");
    PADS.forEach((p, i) => {
      const b = document.createElement("button");
      b.type = "button"; b.className = "pad"; b.dataset.pad = String(i);
      const name = document.createElement("b"); name.textContent = p.name;
      const sub = document.createElement("span"); sub.textContent = noteName(p.n);
      b.append(name, sub);
      box.appendChild(b);
    });
  }
  function buildKeys() {
    const box = $("keys");
    const row = document.createElement("div");
    row.className = "keys";
    for (let n = 36; n <= 84; n++) {
      const black = NAMES[n%12].includes("#");
      const el = document.createElement("div");
      el.className = "key " + (black ? "b" : "w");
      el.dataset.midi = String(n);
      if (!black && n%12 === 0) el.innerHTML = "<em>C" + (Math.floor(n/12)-1) + "</em>";
      row.appendChild(el);
    }
    box.appendChild(row);
    const keyAt = (x, y) => {
      const stack = document.elementsFromPoint(x, y);
      return stack.find((el) => el.dataset && el.dataset.midi);
    };
    row.addEventListener("pointerdown", async (ev) => {
      ev.preventDefault();
      try { row.setPointerCapture(ev.pointerId); } catch (_) {}
      try { await ensure(); } catch (_) { return; }
      const k = keyAt(ev.clientX, ev.clientY);
      if (!k) return;
      const n = +k.dataset.midi;
      ptrNote.set(ev.pointerId, n);
      noteOn(n, 0.9);
    });
    row.addEventListener("pointermove", (ev) => {
      if (!ptrNote.has(ev.pointerId)) return;
      const k = keyAt(ev.clientX, ev.clientY);
      const n = k ? +k.dataset.midi : null;
      const prev = ptrNote.get(ev.pointerId);
      if (n === prev) return;
      if (prev != null) noteOff(prev);
      if (n != null) noteOn(n, 0.88);
      ptrNote.set(ev.pointerId, n);
    });
    const end = (ev) => {
      const n = ptrNote.get(ev.pointerId);
      if (n != null) noteOff(n);
      ptrNote.delete(ev.pointerId);
    };
    row.addEventListener("pointerup", end);
    row.addEventListener("pointercancel", end);
  }

  function nudge(dir) {
    if (!dial) return;
    const span = dial.max - dial.min;
    dial.set(clamp(dial.get() + dir * span / 60, dial.min, dial.max));
    paintAll();
  }
  const fileInput = document.createElement("input");
  fileInput.type = "file";
  fileInput.accept = "application/json";
  fileInput.hidden = true;
  fileInput.addEventListener("change", async () => {
    const f = fileInput.files && fileInput.files[0];
    fileInput.value = "";
    if (!f) return;
    let data = null;
    try { data = JSON.parse(await f.text()); }
    catch (_) { status("JSON ungültig"); return; }
    if (!data || typeof data !== "object") { status("JSON ungültig"); return; }
    if (Array.isArray(data.patches)) {
      bank = data;
      buildBanks();
      if (bank.patches[0]) applyPatch(bank.patches[0]);
      else status("Bank leer");
    } else if (data.parts || data.master || data.name) applyPatch(data);
    else status("JSON ohne Patch");
  });
  document.body.appendChild(fileInput);

  chassis.addEventListener("click", async (ev) => {
    const b = ev.target.closest("button");
    if (!b || !chassis.contains(b)) return;
    if (b.dataset.assign) { assign = b.dataset.assign; paintAll(); return; }
    if (b.dataset.page) { page = b.dataset.page; paintAll(); renderPage(); return; }
    if (b.dataset.bank != null) {
      const i = +b.dataset.bank;
      const list = bank.patches || [];
      const chosen = i === 7 ? (userPatch || list[7] || list[0]) : list[i];
      if (!chosen) { status("Bank leer"); return; }
      applyPatch(chosen);
      return;
    }
    if (b.dataset.patch) {
      applyPatch((bank.patches||[]).find((p) => p.id === b.dataset.patch));
      return;
    }
    if (b.dataset.osc) {
      parts[selI].osc = b.dataset.osc;
      renderPage();
      schedulePersist();
      return;
    }
    if (b.dataset.pad != null) {
      try { await ensure(); } catch (_) { return; }
      hitPad(+b.dataset.pad);
      b.classList.add("hit");
      setTimeout(() => b.classList.remove("hit"), 120);
      return;
    }
    if (b.dataset.sel != null && ev.target === b) return;
    if (b.dataset.dev) {
      const i = +b.dataset.slot;
      const dev = deviceById(b.dataset.dev);
      if (!dev || !racks[i]) return;
      racks[i].id = dev.id;
      racks[i].on = true;
      if (dev.osc) {
        parts[selI].osc = dev.osc;
        parts[selI].on = true;
        if (started) pushBus(selI);
      }
      rackPick = -1;
      applyRacks();
      schedulePersist();
      renderPage();
      status(dev.name + " · Rack " + (i + 1));
      return;
    }
    const act = b.dataset.act;
    if (!act) return;
    if (act === "theme") { setTheme(b.dataset.theme); schedulePersist(); }
    else if (act === "bg") setBg(!bgOn);
    else if (act === "hold") { swLatch = !swLatch; $("sw1").classList.toggle("on", swLatch); if (!holdOn()) liftHold(); }
    else if (act === "oct") { octDown = !octDown; $("sw2").classList.toggle("on", octDown); }
    else if (act === "inc") nudge(1);
    else if (act === "dec") nudge(-1);
    else if (act === "exit") { page = "combi"; panic(); paintAll(); renderPage(); }
    else if (act === "enter") { schedulePersist(); status("Session liegt im Gerät"); }
    else if (act === "tap") tap();
    else if (act === "rec") startRec();
    else if (act === "stop") stopRec();
    else if (act === "export") askExport();
    else if (act === "line") toggleLine();
    else if (act === "rack") { rackPick = rackPick === +b.dataset.slot ? -1 : +b.dataset.slot; renderPage(); }
    else if (act === "rack-x") {
      racks[+b.dataset.slot] = emptyRack();
      rackPick = -1;
      applyRacks();
      schedulePersist();
      renderPage();
    }
    else if (act === "rack-by") {
      const i = +b.dataset.slot;
      racks[i].on = !racks[i].on;
      applyRacks();
      schedulePersist();
      renderPage();
    }
    else if (act === "save") {
      userPatch = snapshot();
      try { localStorage.setItem("rn-sx-user", JSON.stringify(userPatch)); } catch (_) {}
      download(new Blob([JSON.stringify(userPatch, null, 2)], {type:"application/json"}), (userPatch.id||"patch")+".json");
    }
    else if (act === "load") fileInput.click();
    else if (act === "user" && userPatch) applyPatch(userPatch);
  });
  chassis.addEventListener("change", (ev) => {
    const t = ev.target;
    if (!(t instanceof HTMLElement)) return;
    if (t.dataset.field) {
      const i = +t.dataset.part;
      const f = t.dataset.field;
      if (t instanceof HTMLInputElement && t.type === "checkbox") parts[i].on = t.checked;
      else if (f === "osc") parts[i].osc = t.value;
      else {
        const num = Number(t.value);
        if (!Number.isFinite(num)) return;
        parts[i][f] = f === "trans" || f === "lo" || f === "hi" ? clamp(Math.round(num), f === "trans" ? -24 : 0, f === "trans" ? 24 : 127) : num;
        if (parts[i].hi < parts[i].lo) parts[i].hi = parts[i].lo;
      }
      if (f === "on" || f === "level") pushBus(i);
      if (f === "pan") setPan(i, parts[i].pan);
      paintAll();
      schedulePersist();
    }
    if (t.id === "divSel") {
      const n = Number(t.value);
      if (Number.isFinite(n)) { delayMul = n; applyMaster(); }
    }
    if (t.id === "midiCh") {
      const n = parseInt(t.value, 10);
      midiCh = Number.isFinite(n) ? clamp(n, 0, 16) : 0;
      try { localStorage.setItem("rn-sx-midi-ch", String(midiCh)); } catch (_) {}
    }
  });
  chassis.addEventListener("input", (ev) => {
    const t = ev.target;
    if (t.id === "patchName") { patchName = t.value; $("patchTitle").textContent = patchName; schedulePersist(); }
    if (t.dataset && t.dataset.rackamt != null) {
      const i = +t.dataset.rackamt;
      const n = Number(t.value);
      if (racks[i] && Number.isFinite(n)) { racks[i].amt = n; applyRacks(); schedulePersist(); }
    }
    if (t.id === "ceilRange") {
      const n = Number(t.value);
      if (Number.isFinite(n)) { master.ceil = n; applyMaster(); }
    }
  });
  chassis.addEventListener("click", (ev) => {
    const row = ev.target.closest("[data-sel]");
    if (!row) return;
    selI = +row.dataset.sel;
    document.querySelectorAll(".rowp").forEach((el) => el.classList.toggle("on", el === row));
    if (assign === "TONE") paintAll();
  });

  const taps = [];
  function tap() {
    const now = performance.now();
    while (taps.length && now - taps[0] > 2200) taps.shift();
    taps.push(now);
    if (taps.length >= 2) {
      let acc = 0;
      for (let i = 1; i < taps.length; i++) acc += taps[i] - taps[i-1];
      bpm = clamp(Math.round(60000 / (acc / (taps.length-1))), 40, 240);
      $("tempoRead").textContent = String(bpm);
      applyMaster();
    }
  }

  function loop() {
    if (started && motion) {
      lfoPhase += 0.02 * (0.3 + master.rate * 5);
      const open = 15000 - master.motion * 9000 + joyY * 2200;
      const wob = Math.sin(lfoPhase) * master.motion * 2400;
      motion.frequency.value = Math.max(140, open + wob);
    }
    if (analyserL) {
      analyserL.getByteTimeDomainData(scopeData);
      let pk = 0;
      for (let i = 0; i < scopeData.length; i++) pk = Math.max(pk, Math.abs(scopeData[i]-128)/128);
      $("mL").style.transform = "scaleY(" + Math.min(1, pk*1.6) + ")";
      analyserR.getByteTimeDomainData(scopeData);
      pk = 0;
      for (let i = 0; i < scopeData.length; i++) pk = Math.max(pk, Math.abs(scopeData[i]-128)/128);
      $("mR").style.transform = "scaleY(" + Math.min(1, pk*1.6) + ")";
      const c = $("scope");
      const g = c.getContext("2d");
      const w = c.width, h = c.height;
      g.clearRect(0, 0, w, h);
      g.strokeStyle = getComputedStyle(chassis).getPropertyValue("--neon").trim() || "#ff2a4a";
      g.lineWidth = 2;
      g.beginPath();
      analyserL.getByteTimeDomainData(scopeData);
      for (let i = 0; i < scopeData.length; i++) {
        const x = i / scopeData.length * w;
        const y = (scopeData[i]/255) * h;
        if (i === 0) g.moveTo(x, y); else g.lineTo(x, y);
      }
      g.stroke();
    }
    requestAnimationFrame(loop);
  }

  const keyDown = new Set();
  window.addEventListener("keydown", (ev) => {
    if (ev.target && ev.target.closest && ev.target.closest("input, select, textarea")) return;
    if (ev.code === "Space") { ev.preventDefault(); spaceDown = true; return; }
    if (ev.key >= "1" && ev.key <= "8") {
      if (ev.repeat) return;
      ensure().then(() => hitPad(+ev.key - 1)).catch(() => {});
      return;
    }
    const n = KEY[ev.key.toLowerCase()];
    if (n == null || ev.repeat || keyDown.has(n)) return;
    keyDown.add(n);
    ensure().then(() => { if (keyDown.has(n)) noteOn(n, 0.88); }).catch(() => {});
  });
  window.addEventListener("keyup", (ev) => {
    if (ev.code === "Space") { spaceDown = false; liftHold(); return; }
    const n = KEY[ev.key && ev.key.toLowerCase()];
    if (n == null) return;
    keyDown.delete(n);
    noteOff(n);
  });
  if (navigator.requestMIDIAccess && !window.Android) {
    navigator.requestMIDIAccess({sysex:false}).then((access) => {
      midiAccess = access;
      const wire = (input) => {
        input.onmidimessage = (m) => onMidi(m.data, input.name || "MIDI");
      };
      for (const input of access.inputs.values()) wire(input);
      access.onstatechange = (e) => {
        const port = e.port;
        if (port && port.type === "input" && port.state === "connected") wire(port);
        paintMidiPorts();
      };
      paintMidiPorts();
    }).catch(() => {});
  }
  let lineStream = null, lineNode = null;
  async function toggleLine() {
    const btn = $("btnLine");
    if (lineStream) {
      lineStream.getTracks().forEach((t) => t.stop());
      try { if (lineNode) lineNode.disconnect(); } catch (_) {}
      lineStream = null; lineNode = null;
      if (btn) btn.classList.remove("on");
      status("Line aus");
      return;
    }
    if (window.Android && Android.askMic) Android.askMic();
    try {
      await ensure();
      lineStream = await navigator.mediaDevices.getUserMedia({
        audio: {echoCancellation:false, noiseSuppression:false, autoGainControl:false}
      });
      lineNode = ctx.createMediaStreamSource(lineStream);
      const g = ctx.createGain();
      g.gain.value = 0.9;
      lineNode.connect(g); g.connect(dry);
      if (btn) btn.classList.add("on");
      status("Line aktiv · USB-Audio oder Chinch über ein Interface, liegt auf dem Master");
    } catch (_) {
      status("Line braucht die Mikrofonfreigabe oder ein USB-Audio-Interface");
    }
  }
  const GEAR = [
    {label:"MPK Mini / LPK", test:/mpk\s*mini|mpkmini|lpk\s*25|lpk25/i, kind:"keys", padCh:9, knobs:[70,71,72,73,74,75,76,77]},
    {label:"MPD / LPD", test:/mpd\s*2|mpd218|mpd226|mpd232|lpd\s*8|lpd8/i, kind:"pads", knobs:[3,9,12,13,14,15,16,17]},
    {label:"APC Key", test:/apc\s*key/i, kind:"keys", padCh:9, faders:[48,49,50,51,52,53,54,55]},
    {label:"APC", test:/apc/i, kind:"grid", faders:[48,49,50,51,52,53,54,55]},
    {label:"MPK", test:/mpk\s*2|mpk225|mpk249|mpk261|mpk88/i, kind:"keys", padCh:9, knobs:[22,23,24,25,26,27,28,29], faders:[12,13,14,15]},
    {label:"MPC", test:/mpc/i, kind:"keys", padCh:9},
    {label:"Traktor / NI", test:/traktor|kontrol|native instruments/i, kind:"mixer", padCh:9, knobs:[20,21,22,23,24,25,26,27], faders:[28,29,30,31]}
  ];
  let gear = null;
  function matchGear(name) {
    if (!name) return null;
    for (let i = 0; i < GEAR.length; i++) if (GEAR[i].test.test(name)) return GEAR[i];
    return null;
  }
  function noteGear(name) {
    const found = matchGear(name) || midiPorts.map(matchGear).find(Boolean) || null;
    if (found && (!gear || gear.label !== found.label)) {
      gear = found;
      status(found.label + " erkannt");
    }
    return gear;
  }
  function isPad(ch, note, g) {
    if (ch === 9) return true;
    if (!g) return false;
    if (g.kind === "pads") return true;
    if (g.kind === "grid" && note < 64) return true;
    if (g.padCh != null && ch === g.padCh) return true;
    return false;
  }
  function setSpec(spec, v127) {
    if (!spec) return;
    spec.set(spec.min + (v127 / 127) * (spec.max - spec.min));
    armDial(spec);
    paintAll();
  }
  function flashPad(i) {
    const el = document.querySelector('.pad[data-pad="'+i+'"]');
    if (!el) return;
    el.classList.add("hit");
    setTimeout(() => el.classList.remove("hit"), 120);
  }
  window.rnMidi = (s, d1, d2, name) => onMidi([s & 255, d1 & 255, d2 & 255], name || "USB");
  window.rnMmc = (cmd) => {
    const n = cmd & 127;
    if (n === 6) startRec();
    else if (n === 2) stopRec();
    midiMark(n === 6 ? "REC" : n === 2 ? "STOP" : "MMC");
  };
  window.rnMidiPorts = (json) => {
    try { midiPorts = JSON.parse(json) || []; } catch (_) { midiPorts = []; }
    paintMidiPorts();
  };
  function paintMidiPorts() {
    const el = $("midiDevs");
    if (!el) return;
    const names = midiPorts.slice();
    if (midiAccess) {
      for (const input of midiAccess.inputs.values()) {
        if (input.state === "disconnected") continue;
        const name = input.name || "MIDI";
        if (names.indexOf(name) < 0) names.push(name);
      }
    }
    el.textContent = (names.length ? names.join(" · ") : "Kein Eingang · USB oder Bluetooth") + (gear ? " · " + gear.label : "");
  }
  function midiMark(text) {
    const dot = $("midiDot");
    const live = $("midiLive");
    if (dot) {
      dot.classList.add("on");
      clearTimeout(midiMark.t);
      midiMark.t = setTimeout(() => dot.classList.remove("on"), 140);
    }
    if (live && text) live.textContent = text;
  }
  function onMidi(data, name) {
    if (!data || data.length < 1) return;
    const run = () => readMidi(data, name);
    if (started && ctx && ctx.state === "running") { run(); return; }
    const job = midiBoot || (midiBoot = ensure().finally(() => { midiBoot = null; }));
    job.then(run).catch(() => {});
  }
  function chanOk(status) {
    if (status >= 0xf0) return true;
    if ((status & 0x0f) === 9) return true;
    if (!midiCh) return true;
    return (status & 0x0f) === midiCh - 1;
  }
  function readMidi(data, name) {
    const status = data[0] & 0xff;
    const d1 = data.length > 1 ? data[1] & 0x7f : 0;
    const d2 = data.length > 2 ? data[2] & 0x7f : 0;
    if (status < 0x80 || status >= 0xf8) return;
    if (!chanOk(status)) return;
    const cmd = status & 0xf0;
    if (cmd === 0x90 || cmd === 0x80) {
      const g = noteGear(name);
      if (isPad(status & 0x0f, d1, g)) {
        if (cmd === 0x90 && d2 > 0) {
          const i = (d1 >= 36 ? d1 - 36 : d1) % 8;
          hitPad(i); flashPad(i); midiMark("Pad " + (i + 1));
        }
        return;
      }
    }
    if (cmd === 0x90 && d2 > 0) { midiMark(name || "Note"); noteOn(d1, d2 / 127); return; }
    if (cmd === 0x80 || (cmd === 0x90 && d2 === 0)) { noteOff(d1); return; }
    if (cmd === 0xe0) {
      bend = (((d2 << 7) | d1) - 8192) / 8192 * 2;
      applyBend(); paintJoy(); midiMark("Pitch");
      return;
    }
    if (cmd === 0xd0) { joyY = (d1 / 127) * 2 - 1; paintJoy(); midiMark("Aftertouch"); return; }
    if (cmd === 0xc0) {
      const list = bank.patches || [];
      const patch = list[d1];
      if (patch) { applyPatch(patch); midiMark(patch.name); }
      return;
    }
    if (cmd !== 0xb0) return;
    const g = noteGear(name);
    if (g && g.knobs) {
      const i = g.knobs.indexOf(d1);
      if (i >= 0) { setSpec((specs()[assign] || [])[i], d2); midiMark("Regler " + (i + 1)); return; }
    }
    if (g && g.faders) {
      const i = g.faders.indexOf(d1);
      if (i >= 0) { setSpec(faderSpecs()[i], d2); midiMark("Fader " + (i + 1)); return; }
    }
    if (d1 === 1) { joyY = (d2 / 127) * 2 - 1; paintJoy(); midiMark("Mod"); return; }
    if (d1 === 7) {
      master.trim = clamp(-18 + (d2 / 127) * 24, -18, 6);
      applyMaster(); paintVol(); midiMark("Volume");
      return;
    }
    if (d1 === 10) { setPan(selI, (d2 / 127) * 2 - 1); paintAll(); midiMark("Pan"); return; }
    if (d1 === 11) { expr = 0.4 + (d2 / 127) * 0.75; paintRibbon(); midiMark("Expr"); return; }
    if (d1 === 64) {
      midiSus = d2 >= 64;
      if (!holdOn()) liftHold();
      midiMark(midiSus ? "Pedal an" : "Pedal aus");
      return;
    }
    if (d1 === 74) {
      setCut(selI, 180 * Math.pow(12000 / 180, d2 / 127));
      paintAll(); midiMark("Helligkeit");
      return;
    }
    if (d1 === 120 || d1 === 123) { panic(); midiSus = false; midiMark("Panic"); return; }
    if (d1 === 121) {
      bend = 0; joyY = 0; expr = 0.9; midiSus = false;
      applyBend(); paintJoy(); paintRibbon();
      if (!holdOn()) liftHold();
      midiMark("Reset");
    }
  }
  document.addEventListener("visibilitychange", () => {
    if (document.visibilityState === "visible" && started && ctx.state === "suspended") ctx.resume().catch(() => {});
  });

  function frameMeterInit() {
    parts = [blank(true), blank(false), blank(false), blank(false)];
    buildControls();
    buildPads();
    buildKeys();
    buildBanks();
    paintAll();
    renderPage();
    loop();
    if (window.Android) {
      $("apkLink").textContent = "INSTALLIERT";
      $("apkLink").removeAttribute("href");
      $("apkLink").classList.add("is-on");
    }
    try { if (localStorage.getItem("rn-sx-bg") === "1") setBg(true, true); } catch (_) {}
    try { userPatch = JSON.parse(localStorage.getItem("rn-sx-user") || "null"); } catch (_) {}
    try { midiCh = clamp(parseInt(localStorage.getItem("rn-sx-midi-ch") || "0", 10) || 0, 0, 16); } catch (_) {}
  }

  async function init() {
    frameMeterInit();
    const text = await fetch("samples/manifest.csv").then((r) => r.text());
    const lines = text.trim().split("\n").slice(1);
    await Promise.all(lines.map(async (line) => {
      const bits = line.trim().split(",");
      if (bits.length < 4) return;
      const fam = bits[0], hz = parseFloat(bits[2]), file = bits[3].trim();
      if (!fam || !file || !Number.isFinite(hz)) return;
      try {
        const res = await fetch("samples/"+file);
        if (!res.ok) return;
        const buf = await res.arrayBuffer();
        if (!samples[fam]) samples[fam] = [];
        samples[fam].push({hz, raw: buf});
      } catch (_) {}
    }));
    try { bank = await fetch("patches/bank.json").then((r) => r.json()); } catch (_) { bank = {patches:[]}; }
    buildBanks();
    let session = null;
    try { session = JSON.parse(localStorage.getItem("rn-sx-session") || "null"); } catch (_) {}
    if (session && session.parts) applyPatch(session, false);
    else if (bank.patches && bank.patches[0]) applyPatch(bank.patches[0], false);
    status("Beta Final 1.0 · erster Anschlag startet den Master");
  }
  init().catch((err) => status(err.message || "Bank fehlt"));
})();
