'use strict';
/*
 * Moje Drogi — nagrywanie przejechanych dróg i statystyki ulic w miejscowościach.
 * Dane: IndexedDB w przeglądarce (trasy, cache geokodowania, liczba ulic w miejscowościach).
 * Mapa: OpenStreetMap. Nazwy ulic/miejscowości: Nominatim. Liczba wszystkich ulic: Overpass API.
 */

const KRAKOW = [50.0614, 19.9366];
const RADIUS_KM = 120;          // obszar, po którym jeździsz
const SAMPLE_M = 200;           // co ile metrów trasy pytamy o nazwę ulicy
const FOLLOW_ZOOM = 19;         // stałe przybliżenie przy śledzeniu pozycji: poziom ulicy z numerami domów
const MIN_STEP_M = 8;           // pomijamy punkty bliżej niż 8 m od poprzedniego
const MAX_ACCURACY_M = 35;      // pomijamy niedokładne odczyty GPS
const NO_STREET = '(droga bez nazwy)';
const NO_TOWN = 'Poza miejscowością';
const NO_DISTRICT = 'Bez podziału na osiedla';
const TRIP_V = 2;               // wersja rozpoznawania ulic (2 = z osiedlami)
const GREEN = '#16A34A';        // kolor przejechanych dróg na mapie

const $ = (s) => document.querySelector(s);
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const nf1 = new Intl.NumberFormat('pl-PL', { maximumFractionDigits: 1 });
const nf0 = new Intl.NumberFormat('pl-PL', { maximumFractionDigits: 0 });
const fmtKm = (m) => (m < 10000 ? nf1 : nf0).format(m / 1000) + ' km';
const fmtDate = (t) => new Date(t).toLocaleDateString('pl-PL', { day: 'numeric', month: 'short', year: 'numeric' });
const fmtDur = (ms) => {
  const s = Math.max(0, Math.round(ms / 1000));
  const h = Math.floor(s / 3600), m = Math.floor((s % 3600) / 60), sec = s % 60;
  return (h ? h + ':' : '') + String(m).padStart(h ? 2 : 1, '0') + ':' + String(sec).padStart(2, '0');
};
function plural(n, one, few, many) {
  if (n === 1) return one;
  const d = n % 10, dd = n % 100;
  return d >= 2 && d <= 4 && (dd < 12 || dd > 14) ? few : many;
}
function el(tag, attrs = {}, ...kids) {
  const e = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k === 'class') e.className = v;
    else if (k.startsWith('on')) e.addEventListener(k.slice(2), v);
    else if (k === 'style') e.style.cssText = v;
    else e.setAttribute(k, v);
  }
  for (const k of kids) if (k != null) e.append(k);
  return e;
}
function dist(a, b) {
  const R = 6371000, r = Math.PI / 180;
  const dLat = (b[0] - a[0]) * r, dLon = (b[1] - a[1]) * r;
  const x = Math.sin(dLat / 2) ** 2 + Math.cos(a[0] * r) * Math.cos(b[0] * r) * Math.sin(dLon / 2) ** 2;
  return 2 * R * Math.asin(Math.sqrt(x));
}
// Punkt trasy: [lat, lon, czas, przerwa?] — 4. pole = 1 oznacza początek nowego odcinka po wznowieniu nagrywania.
function trackLen(p) { let s = 0; for (let i = 1; i < p.length; i++) if (!p[i][3]) s += dist(p[i - 1], p[i]); return s; }
function segmentsOf(p) {
  const out = [];
  let cur = [];
  for (const q of p) {
    if (q[3] && cur.length) { out.push(cur); cur = []; }
    cur.push([q[0], q[1]]);
  }
  if (cur.length) out.push(cur);
  return out;
}
const activeMs = (t, now = Date.now()) => ((t.paused ? t.pausedAt : t.end ?? now) - t.start) - (t.pausedMs || 0);

/* ---------------- IndexedDB ---------------- */
let idb;
function openDb() {
  return new Promise((res, rej) => {
    const r = indexedDB.open('moje-drogi', 1);
    r.onupgradeneeded = () => {
      const d = r.result;
      d.createObjectStore('trips', { keyPath: 'id' });
      d.createObjectStore('geo', { keyPath: 'k' });
      d.createObjectStore('towns', { keyPath: 'name' });
    };
    r.onsuccess = () => res(r.result);
    r.onerror = () => rej(r.error);
  });
}
function req(store, mode, fn) {
  return new Promise((res, rej) => {
    const t = idb.transaction(store, mode);
    const r = fn(t.objectStore(store));
    t.oncomplete = () => res(r ? r.result : undefined);
    t.onerror = () => rej(t.error);
    t.onabort = () => rej(t.error);
  });
}
const dbAll = (s) => req(s, 'readonly', (o) => o.getAll());
const dbGet = (s, k) => req(s, 'readonly', (o) => o.get(k));
const dbPut = (s, v) => req(s, 'readwrite', (o) => o.put(v));
const dbDel = (s, k) => req(s, 'readwrite', (o) => o.delete(k));

/* ---------------- Stan ---------------- */
const state = {
  trips: [],
  townMeta: {},       // name -> { total, names[], areaName }
  agg: {},            // name -> { name, m, streets: {name: {m, n}}, trips: [], last, pt }
  rec: null,          // nagrywana trasa
  selected: null,     // wybrana miejscowość
  showVisited: true,
  follow: true,
  sort: 'last',
  detailTab: 'streets',
  focus: null,        // miejscowość wybrana w wyszukiwarce: { name, lat, lon }
  filter: '',         // filtr listy miejscowości
  streetFilter: '',   // filtr zbiorczej listy ulic
};

// porównywanie nazw bez wielkości liter i polskich znaków („lodz” znajdzie „Łódź”)
const norm = (s) => s.toLowerCase().replace(/ł/g, 'l').normalize('NFD').replace(/[̀-ͯ]/g, '').trim();

function setStatus(msg) { $('#status').textContent = msg || ''; }

/* ---------------- Mapa ---------------- */
let map, visitedLayer, recLine, posMarker, accCircle;
function initMap() {
  map = L.map('map', { preferCanvas: true, zoomControl: false, attributionControl: true }).setView(KRAKOW, 9);
  L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png', {
    maxZoom: 19,
    attribution: '&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a>',
  }).addTo(map);
  L.circle(KRAKOW, { radius: RADIUS_KM * 1000, color: '#64748B', weight: 1.5, dashArray: '6 8', fill: false, interactive: false }).addTo(map);
  visitedLayer = L.layerGroup().addTo(map);
  recPast = L.layerGroup().addTo(map);
  recLine = L.polyline([], { color: '#EA580C', weight: 6, opacity: 0.95 }).addTo(map);
  map.on('dragstart', () => setFollow(false));
}
function drawTrips() {
  visitedLayer.clearLayers();
  for (const t of state.trips) {
    if (t.recording || t.points.length < 2) continue;
    L.polyline(segmentsOf(t.points), { color: GREEN, weight: 5, opacity: 0.85, interactive: false }).addTo(visitedLayer);
  }
}
function showPos(lat, lon, acc) {
  if (!posMarker) {
    posMarker = L.marker([lat, lon], { icon: L.divIcon({ className: '', html: '<div class="pos-dot"></div>', iconSize: [18, 18], iconAnchor: [9, 9] }), interactive: false, keyboard: false }).addTo(map);
    accCircle = L.circle([lat, lon], { radius: acc, color: '#EA580C', weight: 1, fillOpacity: 0.08, interactive: false }).addTo(map);
  } else {
    posMarker.setLatLng([lat, lon]);
    accCircle.setLatLng([lat, lon]).setRadius(acc);
  }
  if (state.follow) map.setView([lat, lon], FOLLOW_ZOOM, { animate: true });
}
function setFollow(on) {
  state.follow = on;
  if (on && posMarker && map) map.setView(posMarker.getLatLng(), FOLLOW_ZOOM); // wróć do siebie w stałym przybliżeniu
  for (const b of [$('#btn-follow'), $('#btn-full-follow')]) {
    b.classList.toggle('on', on);
    b.setAttribute('aria-pressed', String(on));
  }
}

/* ---------------- Mapa na cały ekran ---------------- */
function setFullMap(on) {
  document.body.classList.toggle('map-full', on);
  if (on) closeResults?.();
  updateRecUi();
  setTimeout(() => map.invalidateSize(), 0); // mapa zmienia rozmiar — Leaflet musi to wiedzieć
  (on ? $('#btn-full-exit') : $('#btn-full')).focus();
}
function fitTown(name) {
  const T = state.agg[name];
  if (!T) return;
  const pts = [];
  for (const t of T.trips) for (const p of t.points) pts.push([p[0], p[1]]);
  if (!pts.length) return;
  setFollow(false);
  showView('view-map');
  map.fitBounds(L.latLngBounds(pts), { padding: [30, 30], maxZoom: 16 });
}

/* ---------------- Nagrywanie GPS ---------------- */
let watchId = null, wakeLock = null, recTimer = null, lastSave = 0, recPast = null;

function startWatch() {
  watchId = navigator.geolocation.watchPosition(onPos, onPosErr, { enableHighAccuracy: true, maximumAge: 0, timeout: 30000 });
  requestWake();
}
async function stopWatch() {
  if (watchId != null) navigator.geolocation.clearWatch(watchId);
  watchId = null;
  try { await wakeLock?.release(); } catch {}
  wakeLock = null;
}

async function pauseRec() {
  const tr = state.rec;
  if (!tr || tr.paused) return;
  await stopWatch();
  tr.paused = true;
  tr.pausedAt = Date.now();
  // dotychczasowy odcinek zostaje na mapie, nowy zacznie się po wznowieniu (bez linii przez przerwę)
  if (recLine.getLatLngs().length) L.polyline(recLine.getLatLngs(), { color: '#EA580C', weight: 6, opacity: 0.6, interactive: false }).addTo(recPast);
  recLine.setLatLngs([]);
  await dbPut('trips', tr);
  updateRecUi();
  setStatus('Nagrywanie wstrzymane. GPS jest wyłączony, przerwa nie liczy się do trasy.');
}

async function resumeRec() {
  const tr = state.rec;
  if (!tr || !tr.paused) return;
  tr.pausedMs = (tr.pausedMs || 0) + (Date.now() - tr.pausedAt);
  tr.paused = false;
  tr.pausedAt = null;
  tr.gapNext = true;
  setFollow(true);
  startWatch();
  await dbPut('trips', tr);
  updateRecUi();
  setStatus('Wznowiono nagrywanie. Szukam sygnału GPS…');
}

async function requestWake() {
  try { if ('wakeLock' in navigator) wakeLock = await navigator.wakeLock.request('screen'); } catch { wakeLock = null; }
}
document.addEventListener('visibilitychange', () => {
  if (document.visibilityState === 'visible' && state.rec && !state.rec.paused && !wakeLock) requestWake();
  if (document.visibilityState === 'hidden' && state.rec) dbPut('trips', state.rec).catch(() => {});
});

async function startRec() {
  if (!('geolocation' in navigator)) { setStatus('Ta przeglądarka nie udostępnia GPS.'); return; }
  if (!window.isSecureContext) { setStatus('GPS działa tylko pod adresem https://. Otwórz aplikację z bezpiecznego adresu.'); return; }
  const trip = { id: 't' + Date.now(), start: Date.now(), end: null, points: [], recording: true, processed: false, source: 'gps', pausedMs: 0, paused: false };
  state.rec = trip;
  recLine.setLatLngs([]);
  recPast.clearLayers();
  setFollow(true);
  startWatch();
  recTimer = setInterval(updateRecUi, 1000);
  updateRecUi();
  setStatus('Szukam sygnału GPS…');
  await dbPut('trips', trip);
}

function onPos(pos) {
  const { latitude: lat, longitude: lon, accuracy } = pos.coords;
  showPos(lat, lon, accuracy);
  const tr = state.rec;
  if (!tr || tr.paused) return;
  if (accuracy > MAX_ACCURACY_M) { setStatus(`Słaby sygnał GPS (±${Math.round(accuracy)} m), czekam…`); return; }
  const p = [+lat.toFixed(6), +lon.toFixed(6), pos.timestamp];
  const last = tr.points[tr.points.length - 1];
  if (tr.gapNext && last) {
    p.push(1); // pierwszy punkt po wznowieniu: nowy odcinek
    tr.gapNext = false;
  } else if (last) {
    const d = dist(last, p);
    if (d < MIN_STEP_M) return;
    const dt = (p[2] - last[2]) / 1000;
    if (dt > 0 && d / dt > 70) return; // skok > 250 km/h — błąd GPS
  }
  tr.points.push(p);
  recLine.addLatLng([p[0], p[1]]);
  setStatus('Nagrywam. Trzymaj aplikację otwartą na ekranie.');
  if (Date.now() - lastSave > 15000) { lastSave = Date.now(); dbPut('trips', tr).catch(() => {}); }
}

function onPosErr(err) {
  if (err.code === 1) {
    setStatus('Brak zgody na lokalizację. Włącz ją w ustawieniach przeglądarki dla tej strony.');
    stopRec();
  } else {
    setStatus('Chwilowo brak sygnału GPS, próbuję dalej…');
  }
}

async function stopRec() {
  const tr = state.rec;
  await stopWatch();
  clearInterval(recTimer);
  state.rec = null;
  recPast.clearLayers();
  updateRecUi();
  if (!tr) return;
  if (tr.paused) tr.pausedMs = (tr.pausedMs || 0) + (Date.now() - tr.pausedAt);
  tr.paused = false;
  tr.pausedAt = null;
  tr.gapNext = false;
  tr.recording = false;
  tr.end = Date.now();
  tr.km = trackLen(tr.points);
  recLine.setLatLngs([]);
  if (tr.points.length < 3) {
    await dbDel('trips', tr.id);
    setStatus('Trasa była za krótka, nie zapisałem jej.');
    return;
  }
  tr.notify = true; // po rozpoznaniu ulic pokaż podsumowanie nowych ulic (i powiadomienie)
  await dbPut('trips', tr);
  state.trips.push(tr);
  drawTrips();
  setStatus(`Zapisano trasę: ${fmtKm(tr.km)}. Rozpoznaję ulice…`);
  processPending();
}

function updateRecUi() {
  const tr = state.rec;
  const on = !!tr;
  $('#btn-rec').classList.toggle('on', on);
  $('#rec-label').textContent = on ? 'Zakończ' : 'Rozpocznij nagrywanie trasy';
  $('#btn-pause').hidden = !on;
  $('#rec-info').hidden = !on;
  if (!on) { updateFullRec(); return; }
  $('#btn-pause').classList.toggle('resume', !!tr.paused);
  $('#pause-label').textContent = tr.paused ? 'Wznów' : 'Wstrzymaj';
  $('#pause-icon').innerHTML = tr.paused ? '<path d="M7 5l12 7-12 7z"/>' : '<path d="M9 5v14M15 5v14"/>';
  $('#rec-info').classList.toggle('paused', !!tr.paused);
  $('#rec-state').textContent = tr.paused ? 'Wstrzymane' : 'Nagrywanie';
  $('#rec-time').textContent = fmtDur(activeMs(tr));
  $('#rec-km').textContent = fmtKm(trackLen(tr.points));
  updateFullRec();
}
// mały pasek nagrywania w trybie pełnoekranowym
function updateFullRec() {
  const tr = state.rec;
  const box = $('#full-rec');
  box.hidden = !tr;
  if (!tr) return;
  const word = el('span', tr.paused ? { class: 'paused-word' } : {}, tr.paused ? 'Wstrzymane' : 'Nagrywanie');
  $('#full-rec-info').replaceChildren(word, ` · ${fmtDur(activeMs(tr))} · ${fmtKm(trackLen(tr.points))}`);
  const btn = $('#btn-full-pause');
  btn.classList.toggle('resume', !!tr.paused);
  btn.setAttribute('aria-label', tr.paused ? 'Wznów nagrywanie' : 'Wstrzymaj nagrywanie');
  $('#full-pause-icon').innerHTML = tr.paused ? '<path d="M7 5l12 7-12 7z"/>' : '<path d="M9 5v14M15 5v14"/>';
}

/* ---------------- Rozpoznawanie ulic (Nominatim) ---------------- */
let lastNominatim = 0, processing = false;

async function reverse(p) {
  const k = p[0].toFixed(4) + ',' + p[1].toFixed(4);
  const cached = await dbGet('geo', k);
  if (cached && 'district' in cached) return cached;
  const wait = lastNominatim + 1100 - Date.now();   // limit Nominatim: 1 zapytanie na sekundę
  if (wait > 0) await sleep(wait);
  lastNominatim = Date.now();
  const url = `https://nominatim.openstreetmap.org/reverse?format=jsonv2&lat=${p[0]}&lon=${p[1]}&zoom=17&addressdetails=1&accept-language=pl`;
  const r = await fetch(url);
  if (!r.ok) throw new Error('nominatim ' + r.status);
  const j = await r.json();
  const a = j.address || {};
  const v = {
    k,
    road: a.road || a.pedestrian || a.footway || null,
    town: a.city || a.town || a.village || a.hamlet || a.municipality || null,
    district: a.suburb || a.city_district || a.quarter || null,
  };
  await dbPut('geo', v);
  return v;
}

async function processTrip(t) {
  const pts = t.points;
  const samples = [{ p: pts[0], d: 0 }];
  let since = 0;
  for (let i = 1; i < pts.length; i++) {
    if (!pts[i][3]) since += dist(pts[i - 1], pts[i]); // przerwy w nagrywaniu nie liczą się do odległości
    if (since >= SAMPLE_M) { samples.push({ p: pts[i], d: since }); since = 0; }
  }
  if (since > 0) samples.push({ p: pts[pts.length - 1], d: since });

  const streets = {}, dstreets = {}, townPts = {};
  for (let i = 0; i < samples.length; i++) {
    setStatus(`Rozpoznaję ulice: ${i + 1} z ${samples.length}`);
    const g = await reverse(samples[i].p);
    const town = g.town || NO_TOWN;
    const street = g.road || NO_STREET;
    streets[town] ??= {};
    streets[town][street] = (streets[town][street] || 0) + samples[i].d;
    const district = g.district || NO_DISTRICT;
    dstreets[town] ??= {};
    dstreets[town][district] ??= {};
    dstreets[town][district][street] = (dstreets[town][district][street] || 0) + samples[i].d;
    townPts[town] ??= [samples[i].p[0], samples[i].p[1]];
  }
  t.streets = streets;
  t.dstreets = dstreets;
  t.townPts = townPts;
  t.v = TRIP_V;
  t.km = trackLen(pts);
  t.processed = true;
  if (!state.trips.includes(t)) return; // trasę usunięto w trakcie rozpoznawania — nie zapisuj jej z powrotem
  await dbPut('trips', t);
}

async function processPending() {
  if (processing) return;
  processing = true;
  try {
    for (const t of state.trips.filter((x) => !x.processed && !x.recording)) {
      await processTrip(t);
      rebuild();
      if (t.notify && state.trips.includes(t)) {
        delete t.notify;
        await dbPut('trips', t);
        const r = newStreetsOf(t);
        showNewStreetsCard(t, r);
        notifyNewStreets(t, r);
      }
    }
    if (!state.rec) setStatus('');
  } catch (e) {
    console.warn(e);
    if (!state.rec) setStatus('Nie mogę teraz rozpoznać ulic (brak internetu?). Spróbuję ponownie później.');
  } finally {
    processing = false;
  }
}
window.addEventListener('online', processPending);

/* ---------------- Wszystkie ulice w miejscowości (Overpass) ---------------- */
const OVERPASS = [
  'https://overpass-api.de/api/interpreter',
  'https://maps.mail.ru/osm/tools/overpass/api/interpreter',
  'https://overpass.kumi.systems/api/interpreter',
];
async function overpass(q) {
  let lastErr;
  for (const url of OVERPASS) {   // publiczne serwery bywają przeciążone — próbujemy po kolei
    try {
      const r = await fetch(url, {
        method: 'POST',
        headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
        body: 'data=' + encodeURIComponent(q),
      });
      if (!r.ok) throw new Error('overpass ' + r.status);
      return await r.json();
    } catch (e) { lastErr = e; }
  }
  throw lastErr;
}

/* ---------------- Osiedla: przypisanie każdej ulicy do osiedla ---------------- */
// Najpierw granica osiedla (jeśli jest w OpenStreetMap), inaczej najbliższy punkt osiedla do 2,5 km.
const DISTRICT_RANK = { suburb: 0, city_district: 1, borough: 1, quarter: 2 };
function ringSegments(e) {
  const segs = [];
  const add = (g) => { for (let i = 1; i < g.length; i++) segs.push([g[i - 1].lat, g[i - 1].lon, g[i].lat, g[i].lon]); };
  if (e.type === 'way' && e.geometry) add(e.geometry);
  if (e.type === 'relation') for (const m of e.members || []) if (m.type === 'way' && m.geometry && m.role !== 'label' && m.role !== 'admin_centre') add(m.geometry);
  return segs;
}
// reguła parzystości: działa na pierścieniach złożonych z wielu odcinków i uwzględnia „dziury”
function insideSegments(lat, lon, segs) {
  let inside = false;
  for (const [y1, x1, y2, x2] of segs) {
    if ((y1 > lat) !== (y2 > lat) && lon < x1 + ((lat - y1) * (x2 - x1)) / (y2 - y1)) inside = !inside;
  }
  return inside;
}
function assignDistricts(els, ways, centersOut = {}) {
  const polys = els
    .filter((e) => (e.type === 'relation' || e.type === 'way') && !e.tags?.highway && e.tags?.name)
    .map((e) => {
      const segs = ringSegments(e);
      const lats = segs.flatMap((x) => [x[0], x[2]]), lons = segs.flatMap((x) => [x[1], x[3]]);
      const rank = e.tags.place ? DISTRICT_RANK[e.tags.place] ?? 3 : 1;
      return { name: e.tags.name, rank, segs, box: [Math.min(...lats), Math.max(...lats), Math.min(...lons), Math.max(...lons)] };
    })
    .filter((p) => p.segs.length >= 3)
    .sort((a, b) => a.rank - b.rank);
  const nodes = els.filter((e) => e.type === 'node' && e.tags?.name && e.lat != null);
  if (!polys.length && !nodes.length) return null;
  const out = {};
  for (const w of ways) {
    const c = w.center;
    let d = null;
    if (c) {
      const p = polys.find((p) => c.lat >= p.box[0] && c.lat <= p.box[1] && c.lon >= p.box[2] && c.lon <= p.box[3] && insideSegments(c.lat, c.lon, p.segs));
      if (p) d = p.name;
      else {
        let best = 2500;
        for (const n of nodes) { const m = dist([c.lat, c.lon], [n.lat, n.lon]); if (m < best) { best = m; d = n.tags.name; } }
      }
    }
    (out[d || NO_DISTRICT] ??= new Set()).add(w.tags.name);
    if (c) (centersOut[d || NO_DISTRICT] ??= []).push([c.lat, c.lon]);
  }
  const res = {};
  for (const [d, set] of Object.entries(out)) res[d] = [...set].sort((a, b) => a.localeCompare(b, 'pl'));
  return res;
}

/* ---------------- Kształty osiedli do mapy ---------------- */
const samePt = (a, b) => Math.abs(a[0] - b[0]) < 1e-7 && Math.abs(a[1] - b[1]) < 1e-7;
// skleja odcinki granicy (członków relacji) w zamknięte pierścienie
function assembleRings(geoms) {
  const parts = geoms.map((g) => g.map((p) => [p.lat, p.lon])).filter((g) => g.length > 1);
  const rings = [];
  while (parts.length) {
    let ring = parts.shift();
    for (let guard = 0; !samePt(ring[0], ring[ring.length - 1]) && guard < 2000; guard++) {
      const end = ring[ring.length - 1];
      const i = parts.findIndex((q) => samePt(q[0], end) || samePt(q[q.length - 1], end));
      if (i < 0) break;
      let q = parts.splice(i, 1)[0];
      if (!samePt(q[0], end)) q = q.slice().reverse();
      ring = ring.concat(q.slice(1));
    }
    if (ring.length >= 4) rings.push(ring);
  }
  return rings;
}
// upraszcza pierścień: punkty co najmniej 25 m od siebie, 5 miejsc po przecinku
function simplifyRing(r, step = 25) {
  const out = [];
  for (const p of r) if (!out.length || dist(out[out.length - 1], p) >= step) out.push([+p[0].toFixed(5), +p[1].toFixed(5)]);
  return out.length >= 3 ? out : null;
}
// otoczka wypukła (algorytm monotoniczny) — przybliżony obszar osiedla bez granicy w OpenStreetMap
function convexHull(pts) {
  const p = [...pts].sort((a, b) => a[1] - b[1] || a[0] - b[0]);
  if (p.length < 3) return null;
  const cross = (o, a, b) => (a[1] - o[1]) * (b[0] - o[0]) - (a[0] - o[0]) * (b[1] - o[1]);
  const lower = [], upper = [];
  for (const q of p) { while (lower.length >= 2 && cross(lower[lower.length - 2], lower[lower.length - 1], q) <= 0) lower.pop(); lower.push(q); }
  for (const q of p.reverse()) { while (upper.length >= 2 && cross(upper[upper.length - 2], upper[upper.length - 1], q) <= 0) upper.pop(); upper.push(q); }
  const h = lower.slice(0, -1).concat(upper.slice(0, -1)).map((q) => [+q[0].toFixed(5), +q[1].toFixed(5)]);
  return h.length >= 3 ? h : null;
}
/** Dla każdego osiedla: granica z OpenStreetMap albo przybliżony obszar z położenia jego ulic. */
function districtShapes(els, districts, centers) {
  if (!districts) return null;
  const out = {};
  for (const d of Object.keys(districts)) {
    if (d === NO_DISTRICT) continue;
    const src = els.find((e) => (e.type === 'relation' || e.type === 'way') && !e.tags?.highway && e.tags?.name === d);
    let rings = [];
    if (src?.type === 'way' && src.geometry) rings = assembleRings([src.geometry]);
    if (src?.type === 'relation') rings = assembleRings((src.members || []).filter((m) => m.type === 'way' && m.geometry && (m.role === 'outer' || m.role === '')).map((m) => m.geometry));
    rings = rings.map((r) => simplifyRing(r)).filter(Boolean);
    if (rings.length) { out[d] = { exact: true, rings }; continue; }
    const pts = centers[d] || [];
    const hull = convexHull(pts);
    if (hull) out[d] = { exact: false, rings: [hull] };
    else if (pts.length) out[d] = { exact: false, center: [+pts[0][0].toFixed(5), +pts[0][1].toFixed(5)] };
  }
  return out;
}

/* ---------------- Mapa osiedli ---------------- */
// skala od szarego (0%) przez coraz ciemniejsze zielenie do pełnej (100%)
const PCT_BINS = [
  { max: 0, color: '#D1D5DB', label: '0%' },
  { max: 24, color: '#DCFCE7', label: '1–24%' },
  { max: 49, color: '#86EFAC', label: '25–49%' },
  { max: 74, color: '#4ADE80', label: '50–74%' },
  { max: 99, color: '#16A34A', label: '75–99%' },
  { max: 100, color: '#14532D', label: '100%' },
];
const pctColor = (pct) => PCT_BINS.find((b) => pct <= b.max).color;
let dmap = null, dLayer = null;

function renderDistrictMap(T, meta, dp) {
  const card = $('#d-map-card');
  const shapes = meta?.shapes;
  const items = (dp || []).filter((D) => shapes?.[D.name]);
  if (!items.length) { card.hidden = true; return; }
  card.hidden = false;
  if (!dmap) {
    dmap = L.map('d-map', { zoomControl: true, scrollWheelZoom: false, attributionControl: true });
    L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png', {
      maxZoom: 19, attribution: '&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a>',
    }).addTo(dmap);
    dLayer = L.featureGroup().addTo(dmap);
  }
  dLayer.clearLayers();
  let approx = false;
  for (const D of items) {
    const sh = shapes[D.name];
    const style = {
      color: sh.exact ? '#14532D' : '#475569', weight: 1.5, dashArray: sh.exact ? null : '5 5',
      fillColor: pctColor(D.pct), fillOpacity: 0.6,
    };
    if (!sh.exact) approx = true;
    const layer = sh.rings ? L.polygon(sh.rings.map((r) => [r]), style) : L.circle(sh.center, { ...style, radius: 300 });
    const pop = el('div', { class: 'dpop' }, el('b', {}, D.name), `${D.pct}% · ${D.hit} z ${D.total} ${plural(D.total, 'ulicy', 'ulic', 'ulic')}`,
      sh.exact ? null : el('div', {}, 'obszar przybliżony'));
    layer.bindPopup(pop).bindTooltip(D.pct + '%', { permanent: true, direction: 'center', className: 'dlabel' });
    dLayer.addLayer(layer);
  }
  const legend = $('#d-legend');
  legend.replaceChildren(...PCT_BINS.map((b) => el('li', {}, el('span', { class: 'sw', style: `background:${b.color}` }), b.label)));
  if (approx) legend.append(el('li', {}, el('span', { class: 'sw approx' }), 'obszar przybliżony'));
  $('#d-map-note').textContent = approx
    ? 'Przerywana linia: OpenStreetMap nie ma granicy tego osiedla, więc obszar wyznaczono z położenia jego ulic.'
    : 'Stuknij osiedle, żeby zobaczyć szczegóły.';
  fitDistrictMap();
}
function fitDistrictMap() {
  if (!dmap || $('#d-map-card').hidden) return;
  dmap.invalidateSize();
  const b = dLayer.getBounds();
  if (b.isValid()) dmap.fitBounds(b, { padding: [16, 16], maxZoom: 16 });
}

/** Procent przejechanych ulic w każdym osiedlu. */
function districtProgress(T, meta) {
  if (!T || !meta?.districts) return null;
  const streetDs = {};
  for (const [d, names] of Object.entries(meta.districts)) for (const s of names) (streetDs[s] ??= new Set()).add(d);
  const seenIn = {};
  for (const D of Object.values(T.districts)) for (const s of Object.keys(D.streets)) (seenIn[s] ??= new Set()).add(D.name);
  return Object.entries(meta.districts).map(([d, names]) => {
    // ulica tylko w jednym osiedlu liczy się zawsze; ulica przez kilka osiedli — tam, gdzie nią jechałeś
    const visited = names.filter((s) => T.streets[s] && (streetDs[s].size === 1 || seenIn[s]?.has(d)));
    const vs = new Set(visited);
    return { name: d, total: names.length, hit: visited.length, pct: Math.round((visited.length / names.length) * 100), visited, missing: names.filter((s) => !vs.has(s)) };
  }).sort((a, b) => (a.name === NO_DISTRICT) - (b.name === NO_DISTRICT) || b.pct - a.pct || a.name.localeCompare(b.name, 'pl'));
}

async function countStreets(name) {
  const T = state.agg[name];
  if (!T?.pt) throw new Error('brak punktu');
  const [lat, lon] = T.pt;
  const areas = await overpass(
    `[out:json][timeout:60];is_in(${lat},${lon})->.a;area.a[boundary=administrative][admin_level~"^(7|8|9|10)$"];out tags;`
  );
  const list = (areas.elements || []).filter((e) => e.tags?.name);
  if (!list.length) throw new Error('brak granic');
  const lc = name.toLowerCase();
  const byLevel = (a, b) => (+b.tags.admin_level) - (+a.tags.admin_level);
  const area =
    list.filter((e) => e.tags.name.toLowerCase() === lc).sort(byLevel)[0] ||
    list.filter((e) => e.tags.name.toLowerCase().includes(lc)).sort(byLevel)[0] ||
    list.sort(byLevel)[0];
  // ulice (ze środkiem odcinka) + osiedla: granice (out geom) i punkty
  const res = await overpass(
    `[out:json][timeout:180];area(id:${area.id})->.t;` +
    `way(area.t)[highway~"^(motorway|trunk|primary|secondary|tertiary|unclassified|residential|living_street|road)$"][name];out tags center;` +
    `(relation(area.t)[boundary=administrative][admin_level~"^(9|10|11)$"][name];` +
    `relation(area.t)[place~"^(suburb|quarter|city_district|borough)$"][name];` +
    `way(area.t)[place~"^(suburb|quarter|city_district|borough)$"][name];);out geom;` +
    `node(area.t)[place~"^(suburb|quarter|city_district|borough)$"][name];out;`
  );
  const els = res.elements || [];
  const ways = els.filter((e) => e.type === 'way' && e.tags?.highway && e.tags?.name);
  const names = [...new Set(ways.map((w) => w.tags.name))].sort((a, b) => a.localeCompare(b, 'pl'));
  const centers = {};
  const districts = assignDistricts(els, ways, centers);
  const meta = {
    name, total: names.length, names, areaName: area.tags.name, checked: Date.now(),
    districts, shapes: districtShapes(els, districts, centers),
  };
  await dbPut('towns', meta);
  state.townMeta[name] = meta;
}

/* ---------------- Agregacja ---------------- */
function rebuild() {
  const agg = {};
  for (const t of state.trips) {
    if (!t.streets) continue;
    for (const [town, sts] of Object.entries(t.streets)) {
      const T = (agg[town] ??= { name: town, m: 0, streets: {}, districts: {}, trips: [], last: 0, pt: null });
      T.trips.push(t);
      T.last = Math.max(T.last, t.start);
      T.pt ??= t.townPts?.[town] || null;
      for (const [s, m] of Object.entries(sts)) {
        T.m += m;
        const S = (T.streets[s] ??= { m: 0, n: 0 });
        S.m += m;
        S.n += 1;
      }
      // osiedla (trasy rozpoznane przed wersją 2 trafiają do „bez podziału”, dopóki się nie przeliczą)
      const byDistrict = t.dstreets?.[town] || { [NO_DISTRICT]: sts };
      for (const [d, dsts] of Object.entries(byDistrict)) {
        const D = (T.districts[d] ??= { name: d, m: 0, streets: {} });
        for (const [s, m] of Object.entries(dsts)) {
          D.m += m;
          const S = (D.streets[s] ??= { m: 0, n: 0, last: 0 });
          S.m += m;
          S.n += 1;
          S.last = Math.max(S.last, t.start);
        }
      }
    }
  }
  state.agg = agg;
  drawTrips();
  renderAll();
}

const namedCount = (T) => Object.keys(T.streets).filter((s) => s !== NO_STREET).length;
function progress(T) {
  const meta = state.townMeta[T.name];
  if (!meta || !meta.total) return null;
  const set = new Set(meta.names);
  const hit = Object.keys(T.streets).filter((s) => set.has(s)).length;
  return { hit, total: meta.total, pct: Math.round((hit / meta.total) * 100) };
}
function townsSorted() {
  const arr = Object.values(state.agg).filter((T) => T.name !== NO_TOWN);
  if (state.sort === 'name') arr.sort((a, b) => a.name.localeCompare(b.name, 'pl'));
  else if (state.sort === 'streets') arr.sort((a, b) => namedCount(b) - namedCount(a));
  else arr.sort((a, b) => b.last - a.last);
  return arr;
}

/* ---------------- Widoki ---------------- */
function renderAll() { renderSheet(); renderTowns(); renderTown(); renderStreets(); renderTrips(); renderStats(); renderShareTab(); }

function sheetTown() {
  if (state.focus) return state.agg[state.focus.name] || null;
  return [...townsSorted()].sort((a, b) => b.last - a.last)[0] || null;
}

function renderSheet() {
  const towns = townsSorted();
  const recent = sheetTown();
  const total = state.trips.reduce((s, t) => s + (t.km || 0), 0);
  $('#st-towns').textContent = towns.length;
  $('#st-total').textContent = fmtKm(total);
  if (state.focus && !recent) {
    $('#sheet-label').textContent = `${state.focus.name} · wyszukana`;
    $('#sheet-big').textContent = '0 ulic';
    $('#st-km').textContent = '0 km';
    return;
  }
  if (!recent) {
    $('#sheet-label').textContent = 'Jeszcze brak przejazdów';
    $('#sheet-big').textContent = '0 ulic';
    $('#st-km').textContent = '0 km';
    return;
  }
  const pr = progress(recent);
  const n = namedCount(recent);
  $('#sheet-label').textContent = `${recent.name} · ${state.focus ? 'wyszukana' : 'ostatnio odwiedzona'}`;
  $('#sheet-big').textContent = pr ? `${pr.pct}% ulic` : `${n} ${plural(n, 'ulica', 'ulice', 'ulic')}`;
  $('#st-km').textContent = fmtKm(recent.m);
}

function renderTowns() {
  const towns = townsSorted();
  const allStreets = towns.reduce((s, T) => s + namedCount(T), 0);
  $('#t-towns').textContent = towns.length;
  $('#t-km').textContent = fmtKm(state.trips.reduce((s, t) => s + (t.km || 0), 0));
  $('#t-streets').textContent = allStreets;
  $('#towns-empty').hidden = towns.length > 0;
  const f = norm(state.filter);
  const shown = f ? towns.filter((T) => norm(T.name).includes(f)) : towns;
  $('#towns-nomatch').hidden = !(towns.length && !shown.length);
  const ul = $('#town-list');
  ul.replaceChildren();
  for (const T of shown) {
    const pr = progress(T);
    const n = namedCount(T);
    const bar = el('i');
    if (pr) { bar.style.width = pr.pct + '%'; if (pr.pct >= 100) bar.className = 'full'; }
    else bar.style.width = '0%';
    const meta = pr
      ? `${pr.hit} z ${pr.total} ulic · ${fmtKm(T.m)} · ${fmtDate(T.last)}`
      : `${n} ${plural(n, 'ulica', 'ulice', 'ulic')} · ${fmtKm(T.m)} · ${fmtDate(T.last)}`;
    ul.append(el('li', {},
      el('button', { class: 'town', type: 'button', onclick: () => openTown(T.name) },
        el('span', { class: 'town-top' },
          el('span', { class: 'town-name' }, T.name),
          el('span', { class: 'town-val' }, pr ? pr.pct + '%' : String(n))),
        el('span', { class: 'bar' }, bar),
        el('span', { class: 'town-meta' }, meta))));
  }
}

function openTown(name) { state.selected = name; renderTown(); showView('view-town'); }

function renderTown() {
  const towns = townsSorted();
  if (!state.selected || !state.agg[state.selected]) state.selected = towns[0]?.name || null;
  const T = state.agg[state.selected];
  const list = $('#d-list');
  list.replaceChildren();
  $('#btn-count').disabled = !T;
  $('#btn-show').disabled = !T;
  if (!T) {
    $('#d-name').textContent = 'Brak danych';
    $('#d-sub').textContent = 'Nagraj pierwszą trasę';
    $('#d-area').textContent = '';
    $('#d-map-card').hidden = true;
    return;
  }
  const pr = progress(T);
  const meta = state.townMeta[T.name];
  const n = namedCount(T);
  const first = Math.min(...T.trips.map((t) => t.start));
  $('#d-name').textContent = T.name;
  $('#d-sub').textContent = `pierwszy przejazd ${fmtDate(first)} · ${T.trips.length} ${plural(T.trips.length, 'przejazd', 'przejazdy', 'przejazdów')}`;
  $('#d-streets').textContent = pr ? pr.hit : n;
  $('#d-total').textContent = meta ? meta.total : '?';
  $('#d-km').textContent = fmtKm(T.m);
  $('#d-trips').textContent = T.trips.length;
  const pct = pr ? pr.pct : 0;
  $('#d-ring-fg').setAttribute('stroke-dasharray', `${(pct / 100) * 251.3} 251.3`);
  $('#d-ring-txt').textContent = pr ? pct + '%' : '?';
  $('#d-ring').setAttribute('aria-label', pr ? `Przejechane ${pct}% ulic` : 'Postęp nieznany — policz wszystkie ulice');
  $('#btn-count').textContent = meta ? 'Policz ulice ponownie' : 'Policz wszystkie ulice';
  $('#d-area').textContent = meta
    ? `Ulice liczone w granicach: ${meta.areaName} (OpenStreetMap, ${fmtDate(meta.checked)}).` +
      (meta.districts === undefined ? ' Policz ponownie, żeby zobaczyć procent dla każdego osiedla.'
        : meta.districts && meta.shapes === undefined ? ' Policz ponownie, żeby zobaczyć mapę osiedli.'
        : meta.districts === null ? ' OpenStreetMap nie dzieli tej miejscowości na osiedla.' : '')
    : 'Kliknij „Policz wszystkie ulice”, żeby zobaczyć, jaki procent miejscowości już przejechałeś.';

  $('#tab-streets').setAttribute('aria-selected', String(state.detailTab === 'streets'));
  $('#tab-trips').setAttribute('aria-selected', String(state.detailTab === 'trips'));

  const dp = districtProgress(T, meta);
  renderDistrictMap(T, meta, dp);
  if (state.detailTab === 'streets' && dp) {
    // tryb z procentami osiedli: każde osiedle z paskiem, przejechane i jeszcze nie
    const inAny = new Set(Object.values(meta.districts).flat());
    for (const D of dp) {
      list.append(districtHead(D));
      for (const s of D.visited) {
        const v = T.streets[s];
        list.append(el('li', {}, el('span', { class: 'd' }), el('span', { class: 'n' }, s), el('span', { class: 'm' }, `${v.n}× · ${fmtKm(v.m)}`)));
      }
      for (const s of D.missing) {
        list.append(el('li', {}, el('span', { class: 'd no' }), el('span', { class: 'n' }, s), el('span', { class: 'm' }, 'jeszcze nie')));
      }
    }
    const other = Object.entries(T.streets).filter(([s]) => !inAny.has(s)).sort((a, b) => b[1].m - a[1].m);
    if (other.length) list.append(groupHead('Inne przejechane drogi', other.length, other.reduce((x, [, v]) => x + v.m, 0)));
    for (const [s, v] of other) {
      list.append(el('li', {}, el('span', { class: 'd' }), el('span', { class: 'n' }, s), el('span', { class: 'm' }, `${v.n}× · ${fmtKm(v.m)}`)));
    }
  } else if (state.detailTab === 'streets') {
    const districts = districtsSorted(T);
    const showHeads = !(districts.length === 1 && districts[0].name === NO_DISTRICT);
    for (const D of districts) {
      const streets = Object.entries(D.streets).sort((a, b) => b[1].m - a[1].m);
      if (showHeads) list.append(groupHead(D.name, streets.filter(([s]) => s !== NO_STREET).length, D.m));
      for (const [s, v] of streets) {
        list.append(el('li', {}, el('span', { class: 'd' }), el('span', { class: 'n' }, s),
          el('span', { class: 'm' }, `${v.n}× · ${fmtKm(v.m)}`)));
      }
    }
    if (meta) {
      const missing = meta.names.filter((s) => !T.streets[s]);
      if (missing.length) list.append(groupHead('Jeszcze nie przejechane', missing.length, null));
      for (const s of missing) {
        list.append(el('li', {}, el('span', { class: 'd no' }), el('span', { class: 'n' }, s), el('span', { class: 'm' }, 'jeszcze nie')));
      }
    }
  } else {
    const trips = [...T.trips].sort((a, b) => b.start - a.start);
    for (const t of trips) {
      const d = new Date(t.start);
      const inTown = Object.values(t.streets[T.name] || {}).reduce((s, m) => s + m, 0);
      const nSt = Object.keys(t.streets[T.name] || {}).filter((s) => s !== NO_STREET).length;
      let armed = false;
      const del = el('button', { class: 'del', type: 'button' }, 'Usuń');
      del.addEventListener('click', async () => {
        if (!armed) { armed = true; del.textContent = 'Na pewno?'; setTimeout(() => { armed = false; del.textContent = 'Usuń'; }, 3000); return; }
        await dbDel('trips', t.id);
        state.trips = state.trips.filter((x) => x.id !== t.id);
        rebuild();
      });
      list.append(el('li', {},
        el('span', { class: 'date' }, el('b', {}, String(d.getDate())), el('span', {}, d.toLocaleDateString('pl-PL', { month: 'short' }))),
        el('span', { class: 'n' }, `${fmtKm(inTown)} w miejscowości, ${nSt} ${plural(nSt, 'ulica', 'ulice', 'ulic')}`,
          el('br'), el('span', { class: 'm' }, `cała trasa ${fmtKm(t.km || 0)}${t.end ? ' · ' + fmtDur(activeMs(t)) : ''}${t.source === 'gpx' ? ' · GPX' : ''}`)),
        del));
    }
  }
}

function districtsSorted(T) {
  return Object.values(T.districts).sort((a, b) =>
    (a.name === NO_DISTRICT) - (b.name === NO_DISTRICT) || b.m - a.m);
}
function districtHead(D) {
  const bar = el('i');
  bar.style.width = D.pct + '%';
  if (D.pct >= 100) bar.className = 'full';
  return el('li', { class: 'group district' },
    el('span', { class: 'dh-top' },
      el('span', { class: 'n' }, D.name),
      el('span', { class: 'dh-pct' }, D.pct + '%')),
    el('span', { class: 'bar' }, bar),
    el('span', { class: 'm' }, `${D.hit} z ${D.total} ${plural(D.total, 'ulicy', 'ulic', 'ulic')}`));
}
function groupHead(name, n, m) {
  return el('li', { class: 'group' },
    el('span', { class: 'n' }, name),
    el('span', { class: 'm' }, `${n} ${plural(n, 'ulica', 'ulice', 'ulic')}${m != null ? ' · ' + fmtKm(m) : ''}`));
}

/* ---------------- Nowe ulice po trasie: karta w aplikacji i powiadomienie ---------------- */
/** Ulice i miejscowości z tej trasy, których nie było na żadnej wcześniejszej trasie. */
function newStreetsOf(t) {
  const seen = new Set(), seenTowns = new Set();
  for (const o of state.trips) {
    if (o === t || !o.processed || o.start >= t.start) continue;
    for (const [town, sts] of Object.entries(o.streets || {})) {
      seenTowns.add(town);
      for (const s of Object.keys(sts)) seen.add(town + '|' + s);
    }
  }
  const byTown = {};
  let count = 0;
  for (const [town, sts] of Object.entries(t.streets || {})) {
    if (town === NO_TOWN) continue;
    for (const s of Object.keys(sts)) {
      if (s === NO_STREET || seen.has(town + '|' + s)) continue;
      (byTown[town] ??= []).push(s);
      count++;
    }
  }
  for (const list of Object.values(byTown)) list.sort((a, b) => a.localeCompare(b, 'pl'));
  const newTowns = Object.keys(t.streets || {}).filter((x) => x !== NO_TOWN && !seenTowns.has(x));
  return { byTown, count, newTowns };
}

function showNewStreetsCard(t, r) {
  const card = $('#ns-card');
  $('#ns-title').textContent = r.count
    ? `${r.count} ${plural(r.count, 'nowa ulica', 'nowe ulice', 'nowych ulic')} z tej trasy`
    : 'Trasa rozpoznana';
  const ul = $('#ns-list');
  ul.replaceChildren();
  if (!r.count) {
    ul.append(el('li', {}, `${fmtKm(t.km || 0)} znanymi już ulicami. Spróbuj następnym razem innej drogi.`));
  }
  for (const [town, streets] of Object.entries(r.byTown).sort((a, b) => b[1].length - a[1].length)) {
    const isNew = r.newTowns.includes(town);
    ul.append(el('li', {},
      el('button', { class: 'ns-town', type: 'button', onclick: () => openTown(town) },
        `${town}${isNew ? ' (nowa miejscowość)' : ''} · ${streets.length} ›`),
      el('div', { class: 'ns-streets' }, ...streets.slice(0, 8).map((s) => el('span', { class: 'ns-chip' }, s)),
        streets.length > 8 ? el('span', { class: 'ns-chip' }, `+${streets.length - 8}`) : null)));
  }
  card.hidden = false;
}

// ---- powiadomienia systemowe ----
const notifySupported = () => 'Notification' in window;
function notifyEnabled() {
  try { return localStorage.getItem('notifyNewStreets') === '1' && notifySupported() && Notification.permission === 'granted'; } catch { return false; }
}
function renderNotifySwitch(msg) {
  const on = notifyEnabled();
  $('#btn-notify').setAttribute('aria-checked', String(on));
  const hint = $('#notify-hint');
  hint.textContent = msg || (on ? 'Po rozpoznaniu ulic dostaniesz powiadomienie z listą nowych ulic.' : '');
  hint.hidden = !hint.textContent;
}
async function toggleNotify() {
  if (notifyEnabled()) {
    try { localStorage.setItem('notifyNewStreets', '0'); } catch {}
    renderNotifySwitch('Powiadomienia wyłączone. Podsumowanie nowych ulic nadal pokaże się w aplikacji.');
    return;
  }
  if (!notifySupported()) {
    renderNotifySwitch('Ta przeglądarka nie obsługuje powiadomień. Na iPhonie działają po dodaniu aplikacji do ekranu początkowego (iOS 16.4 lub nowszy).');
    return;
  }
  let perm = Notification.permission;
  if (perm === 'default') { try { perm = await Notification.requestPermission(); } catch { perm = 'denied'; } }
  if (perm !== 'granted') {
    renderNotifySwitch('Powiadomienia są zablokowane. Włącz je w ustawieniach telefonu dla tej aplikacji i spróbuj ponownie.');
    return;
  }
  try { localStorage.setItem('notifyNewStreets', '1'); } catch {}
  renderNotifySwitch();
}

function notifyText(t, r) {
  const parts = Object.entries(r.byTown).sort((a, b) => b[1].length - a[1].length).map(([town, s]) =>
    `${town}: ${s.slice(0, 3).join(', ')}${s.length > 3 ? ` i ${s.length - 3} ${plural(s.length - 3, 'inna', 'inne', 'innych')}` : ''}`);
  const towns = r.newTowns.length ? ` Nowe miejscowości: ${r.newTowns.join(', ')}.` : '';
  return {
    title: `${r.count} ${plural(r.count, 'nowa ulica', 'nowe ulice', 'nowych ulic')} na trasie (${fmtKm(t.km || 0)})`,
    body: parts.join(' · ') + (towns ? '.' + towns : ''),
  };
}
async function notifyNewStreets(t, r) {
  if (!r.count || !notifyEnabled()) return;
  const { title, body } = notifyText(t, r);
  const opts = { body, icon: 'icon.svg', badge: 'icon.svg', tag: 'trip-' + t.id, data: { url: './' } };
  try {
    const reg = await navigator.serviceWorker?.getRegistration();
    if (reg) await reg.showNotification(title, opts);
    else new Notification(title, opts);
  } catch (e) {
    console.warn('powiadomienie', e);
  }
}

/* ---------------- Wszystkie ulice w jednym miejscu ---------------- */
function allStreetRows() {
  const rows = [];
  for (const T of Object.values(state.agg)) {
    if (T.name === NO_TOWN) continue;
    for (const D of Object.values(T.districts)) {
      for (const [s, v] of Object.entries(D.streets)) {
        if (s === NO_STREET) continue;
        rows.push({ town: T.name, district: D.name, street: s, n: v.n, m: v.m, last: v.last });
      }
    }
  }
  return rows;
}

function renderStreets() {
  const rows = allStreetRows();
  const f = norm(state.streetFilter || '');
  const shown = f ? rows.filter((r) => norm(`${r.street} ${r.district} ${r.town}`).includes(f)) : rows;
  const uniq = new Set(rows.map((r) => r.town + '|' + r.street)).size;
  $('#s-count').textContent = uniq;
  $('#s-towns').textContent = new Set(rows.map((r) => r.town)).size;
  $('#s-districts').textContent = new Set(rows.filter((r) => r.district !== NO_DISTRICT).map((r) => r.town + '|' + r.district)).size;
  $('#streets-empty').hidden = rows.length > 0;
  $('#streets-nomatch').hidden = !(rows.length && !shown.length);
  $('#btn-csv').disabled = !rows.length;

  const box = $('#all-streets');
  box.replaceChildren();
  const byTown = new Map();
  for (const r of shown) {
    if (!byTown.has(r.town)) byTown.set(r.town, new Map());
    const dm = byTown.get(r.town);
    if (!dm.has(r.district)) dm.set(r.district, []);
    dm.get(r.district).push(r);
  }
  const towns = [...byTown.keys()].sort((a, b) => a.localeCompare(b, 'pl'));
  for (const town of towns) {
    const dm = byTown.get(town);
    const count = [...dm.values()].reduce((x, a) => x + a.length, 0);
    const ul = el('ul', { class: 'card list' });
    const ds = [...dm.keys()].sort((a, b) => (a === NO_DISTRICT) - (b === NO_DISTRICT) || a.localeCompare(b, 'pl'));
    const showHeads = !(ds.length === 1 && ds[0] === NO_DISTRICT);
    for (const d of ds) {
      const items = dm.get(d).sort((a, b) => a.street.localeCompare(b.street, 'pl'));
      const dpd = districtProgress(state.agg[town], state.townMeta[town])?.find((x) => x.name === d);
      if (showHeads) ul.append(dpd ? districtHead(dpd) : groupHead(d, items.length, items.reduce((x, r) => x + r.m, 0)));
      for (const r of items) {
        ul.append(el('li', {}, el('span', { class: 'd' }), el('span', { class: 'n' }, r.street),
          el('span', { class: 'm' }, `${r.n}× · ${fmtDate(r.last)}`)));
      }
    }
    const head = el('button', { class: 'town-link', type: 'button', onclick: () => openTown(town) },
      el('span', {}, town), el('span', { class: 'm' }, `${count} ${plural(count, 'ulica', 'ulice', 'ulic')} ›`));
    box.append(el('section', { class: 'street-town' }, head, ul));
  }
}

function exportCsv() {
  const rows = allStreetRows().sort((a, b) =>
    a.town.localeCompare(b.town, 'pl') || a.district.localeCompare(b.district, 'pl') || a.street.localeCompare(b.street, 'pl'));
  const q = (v) => '"' + String(v).replace(/"/g, '""') + '"';
  const lines = [['Miejscowość', 'Osiedle', 'Ulica', 'Liczba przejazdów', 'Km', 'Ostatni przejazd'].map(q).join(';')];
  for (const r of rows) {
    lines.push([r.town, r.district === NO_DISTRICT ? '' : r.district, r.street, r.n,
      (r.m / 1000).toFixed(2).replace('.', ','), new Date(r.last).toISOString().slice(0, 10)].map(q).join(';'));
  }
  // BOM, żeby Excel poprawnie pokazał polskie znaki
  const blob = new Blob(['\ufeff' + lines.join('\r\n')], { type: 'text/csv;charset=utf-8' });
  const a = el('a', { href: URL.createObjectURL(blob), download: `moje-drogi-ulice-${new Date().toISOString().slice(0, 10)}.csv` });
  document.body.append(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(a.href), 5000);
}

/* ---------------- Nagrane trasy: podgląd i usuwanie ---------------- */
const tripSel = { on: false, ids: new Set() };
let highlight = null;

function tripTowns(t) {
  return Object.keys(t.streets || {}).filter((x) => x !== NO_TOWN);
}

async function deleteTrips(ids) {
  const set = new Set(ids);
  for (const id of set) await dbDel('trips', id);
  state.trips = state.trips.filter((t) => !set.has(t.id));
  tripSel.ids.clear();
  if (highlight && set.has(highlight.tripId)) { highlight.remove(); highlight = null; }
  rebuild();
  setStatus(`Usunięto ${set.size} ${plural(set.size, 'trasę', 'trasy', 'tras')}.`);
}

function showTripOnMap(t) {
  if (highlight) highlight.remove();
  highlight = L.polyline(segmentsOf(t.points), { color: '#1D4ED8', weight: 7, opacity: 0.9 }).addTo(map);
  highlight.tripId = t.id;
  setFollow(false);
  showView('view-map');
  map.fitBounds(highlight.getBounds(), { padding: [30, 30], maxZoom: 16 });
  setStatus(`Pokazuję trasę z ${fmtDate(t.start)} (niebieska linia).`);
}

function renderTrips() {
  const trips = state.trips.filter((t) => !t.recording).sort((a, b) => b.start - a.start);
  const total = trips.reduce((x, t) => x + (t.km || 0), 0);
  for (const id of [...tripSel.ids]) if (!trips.some((t) => t.id === id)) tripSel.ids.delete(id);
  $('#btn-trips').textContent = `Nagrane trasy (${trips.length})`;
  $('#tr-sub').textContent = `${trips.length} ${plural(trips.length, 'trasa', 'trasy', 'tras')} · ${fmtKm(total)}`;
  $('#tr-empty').hidden = trips.length > 0;
  $('#tr-tools').hidden = trips.length === 0;
  if (!trips.length) tripSel.on = false;
  $('#btn-select').setAttribute('aria-pressed', String(tripSel.on));
  $('#btn-select').textContent = tripSel.on ? 'Gotowe' : 'Zaznacz';
  $('#tr-selbar').hidden = !tripSel.on;
  $('#tr-selcount').textContent = `Zaznaczono ${tripSel.ids.size}`;
  $('#btn-del-sel').disabled = tripSel.ids.size === 0;
  $('#btn-del-sel').textContent = tripSel.ids.size ? `Usuń zaznaczone (${tripSel.ids.size})` : 'Usuń zaznaczone';

  const ul = $('#tr-list');
  ul.hidden = trips.length === 0;
  ul.replaceChildren();
  let lastDay = null;
  for (const t of trips) {
    const d = new Date(t.start);
    const day = dayKey(t.start);
    if (day !== lastDay) {
      lastDay = day;
      const dayTrips = trips.filter((x) => dayKey(x.start) === day);
      const dayM = dayTrips.reduce((x, y) => x + (y.km || 0), 0);
      const head = el('li', { class: 'group day-head' },
        el('span', { class: 'n' }, dayLabel(day)),
        el('span', { class: 'm' }, `${dayTrips.length} ${plural(dayTrips.length, 'trasa', 'trasy', 'tras')} · ${fmtKm(dayM)}`));
      ul.append(head);
    }
    const towns = tripTowns(t);
    const when = d.toLocaleDateString('pl-PL', { day: 'numeric', month: 'short', year: 'numeric' }) + ', ' +
      d.toLocaleTimeString('pl-PL', { hour: '2-digit', minute: '2-digit' });
    const whenShort = 'godz. ' + d.toLocaleTimeString('pl-PL', { hour: '2-digit', minute: '2-digit' });
    const meta = `${fmtKm(t.km || 0)}${t.end ? ' · ' + fmtDur(activeMs(t)) : ''}${t.pausedMs > 60000 ? ' (bez przerw)' : ''}${t.source === 'gpx' ? ' · GPX' : ''}`;
    const where = t.processed ? (towns.length ? towns.join(', ') : 'poza miejscowościami') : 'rozpoznaję ulice…';
    const id = 'trip-' + t.id;
    const info = el(tripSel.on ? 'label' : 'span', tripSel.on ? { class: 'tinfo', for: id } : { class: 'tinfo' },
      el('b', {}, whenShort), el('span', { class: 'm' }, meta), el('span', { class: 'm' }, where));
    const li = el('li', {});
    if (tripSel.on) {
      const cb = el('input', { type: 'checkbox', id });
      cb.checked = tripSel.ids.has(t.id);
      cb.addEventListener('change', () => { if (cb.checked) tripSel.ids.add(t.id); else tripSel.ids.delete(t.id); renderTrips(); });
      li.append(cb, info);
    } else {
      li.append(info,
        el('button', { class: 'tbtn', type: 'button', 'aria-label': `Pokaż na mapie trasę z ${when}`, onclick: () => showTripOnMap(t) },
          svgIcon('M9 4l-6 2v14l6-2 6 2 6-2V4l-6 2-6-2z M9 4v14 M15 6v14')),
        el('button', {
          class: 'tbtn del', type: 'button', 'aria-label': `Usuń trasę z ${when}`,
          onclick: () => { if (confirm(`Usunąć trasę z ${when} (${fmtKm(t.km || 0)})?`)) deleteTrips([t.id]); },
        }, svgIcon('M4 7h16 M10 11v6 M14 11v6 M6 7l1 13h10l1-13 M9 7V4h6v3')));
    }
    ul.append(li);
  }
}
/* ---------------- Udostępnianie tras z danego dnia ---------------- */
const dayKey = (t) => { const d = new Date(t); return `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}-${String(d.getDate()).padStart(2, '0')}`; };
function dayLabel(key) {
  const [y, m, d] = key.split('-').map(Number);
  const date = new Date(y, m - 1, d);
  const today = dayKey(Date.now()), yest = dayKey(Date.now() - 86400000);
  const base = date.toLocaleDateString('pl-PL', { weekday: 'long', day: 'numeric', month: 'long', year: 'numeric' });
  return key === today ? `Dziś, ${base}` : key === yest ? `Wczoraj, ${base}` : base.charAt(0).toUpperCase() + base.slice(1);
}

/** Podsumowanie dnia: trasy, km, czas jazdy, nowe ulice (pierwszy raz przejechane tego dnia). */
function daySummary(key) {
  const trips = state.trips.filter((t) => !t.recording && dayKey(t.start) === key).sort((a, b) => a.start - b.start);
  const m = trips.reduce((x, t) => x + (t.km || 0), 0);
  const ms = trips.reduce((x, t) => x + (t.end ? activeMs(t) : 0), 0);
  const dayStart = Math.min(...trips.map((t) => t.start));
  const seen = new Set();
  for (const o of state.trips) {
    if (o.recording || o.start >= dayStart) continue;
    for (const [town, sts] of Object.entries(o.streets || {})) for (const s of Object.keys(sts)) seen.add(town + '|' + s);
  }
  const fresh = {};
  for (const t of trips) for (const [town, sts] of Object.entries(t.streets || {})) {
    if (town === NO_TOWN) continue;
    for (const s of Object.keys(sts)) {
      const k = town + '|' + s;
      if (s === NO_STREET || seen.has(k)) continue;
      seen.add(k);
      fresh[town] = (fresh[town] || 0) + 1;
    }
  }
  const newCount = Object.values(fresh).reduce((x, n) => x + n, 0);
  const towns = [...new Set(trips.flatMap((t) => tripTowns(t)))];
  return { key, trips, m, ms, fresh, newCount, towns };
}

function shareText(S) {
  const parts = [`Moje Drogi · ${dayLabel(S.key)}`,
    `${S.trips.length} ${plural(S.trips.length, 'trasa', 'trasy', 'tras')}, ${fmtKm(S.m)}${S.ms ? `, ${fmtDur(S.ms)} jazdy` : ''}.`];
  if (S.newCount) {
    const per = Object.entries(S.fresh).sort((a, b) => b[1] - a[1]).map(([t, n]) => `${t} ${n}`).join(', ');
    parts.push(`Nowe ulice: ${S.newCount} (${per}).`);
  }
  if (S.towns.length) parts.push(`Miejscowości: ${S.towns.join(', ')}.`);
  return parts.join('\n');
}

/** Plik GPX z trasami dnia: osobny ślad dla każdej trasy, osobny odcinek po każdej przerwie. */
function buildGpx(S) {
  const esc = (x) => String(x).replace(/[<>&"]/g, (c) => ({ '<': '&lt;', '>': '&gt;', '&': '&amp;', '"': '&quot;' }[c]));
  const trk = S.trips.map((t) => {
    const segs = [];
    let cur = [];
    for (const p of t.points) {
      if (p[3] && cur.length) { segs.push(cur); cur = []; }
      cur.push(p);
    }
    if (cur.length) segs.push(cur);
    const name = `Trasa ${new Date(t.start).toLocaleTimeString('pl-PL', { hour: '2-digit', minute: '2-digit' })}`;
    return `  <trk><name>${esc(name)}</name>\n` + segs.map((seg) => '    <trkseg>\n' + seg.map((p) =>
      `      <trkpt lat="${p[0]}" lon="${p[1]}">${p[2] > 1e12 ? `<time>${new Date(p[2]).toISOString()}</time>` : ''}</trkpt>`).join('\n') + '\n    </trkseg>').join('\n') + '\n  </trk>';
  }).join('\n');
  return `<?xml version="1.0" encoding="UTF-8"?>\n<gpx version="1.1" creator="Moje Drogi" xmlns="http://www.topografix.com/GPX/1/1">\n  <metadata><name>${esc('Moje Drogi ' + S.key)}</name></metadata>\n${trk}\n</gpx>\n`;
}

// --- obraz 1080×1350: nagłówek z datą i liczbami, mapa z trasami, stopka ---
const IMG_W = 1080, IMG_H = 1350, MAP_TOP = 250, MAP_H = 980;
const projX = (lon, z) => ((lon + 180) / 360) * 256 * 2 ** z;
const projY = (lat, z) => { const r = (lat * Math.PI) / 180; return ((1 - Math.log(Math.tan(r) + 1 / Math.cos(r)) / Math.PI) / 2) * 256 * 2 ** z; };
function loadTile(url) {
  return new Promise((res) => {
    const img = new Image();
    img.crossOrigin = 'anonymous';
    const timer = setTimeout(() => res(null), 8000);
    img.onload = () => { clearTimeout(timer); res(img); };
    img.onerror = () => { clearTimeout(timer); res(null); };
    img.src = url;
  });
}
async function drawShareImage(canvas, S, withTiles = true) {
  const ctx = canvas.getContext('2d');
  try { await document.fonts?.ready; } catch {}
  ctx.fillStyle = '#FFFFFF';
  ctx.fillRect(0, 0, IMG_W, IMG_H);
  // nagłówek
  ctx.fillStyle = '#15803D';
  ctx.font = '700 34px "Space Grotesk", Inter, sans-serif';
  ctx.fillText('Moje Drogi', 60, 82);
  ctx.fillStyle = '#111827';
  ctx.font = '700 52px "Space Grotesk", Inter, sans-serif';
  ctx.fillText(dayLabel(S.key), 60, 150, IMG_W - 120);
  ctx.fillStyle = '#4B5563';
  ctx.font = '500 34px Inter, sans-serif';
  const line = `${fmtKm(S.m)} · ${S.trips.length} ${plural(S.trips.length, 'trasa', 'trasy', 'tras')}${S.ms ? ' · ' + fmtDur(S.ms) + ' jazdy' : ''}${S.newCount ? ` · ${S.newCount} ${plural(S.newCount, 'nowa ulica', 'nowe ulice', 'nowych ulic')}` : ''}`;
  ctx.fillText(line, 60, 210, IMG_W - 120);

  // mapa: dobór przybliżenia tak, żeby wszystkie trasy się zmieściły
  const pts = S.trips.flatMap((t) => t.points);
  let z = 17;
  for (; z > 3; z--) {
    const xs = pts.map((p) => projX(p[1], z)), ys = pts.map((p) => projY(p[0], z));
    if (Math.max(...xs) - Math.min(...xs) <= IMG_W - 140 && Math.max(...ys) - Math.min(...ys) <= MAP_H - 140) break;
  }
  const xs = pts.map((p) => projX(p[1], z)), ys = pts.map((p) => projY(p[0], z));
  const ox = (Math.min(...xs) + Math.max(...xs)) / 2 - IMG_W / 2;
  const oy = (Math.min(...ys) + Math.max(...ys)) / 2 - MAP_H / 2;
  ctx.save();
  ctx.beginPath();
  ctx.rect(0, MAP_TOP, IMG_W, MAP_H);
  ctx.clip();
  ctx.fillStyle = '#E9ECE6';
  ctx.fillRect(0, MAP_TOP, IMG_W, MAP_H);
  if (withTiles) {
    const jobs = [];
    for (let tx = Math.floor(ox / 256); tx <= Math.floor((ox + IMG_W) / 256); tx++) {
      for (let ty = Math.floor(oy / 256); ty <= Math.floor((oy + MAP_H) / 256); ty++) {
        jobs.push(loadTile(`https://tile.openstreetmap.org/${z}/${tx}/${ty}.png`).then((img) => img && ctx.drawImage(img, tx * 256 - ox, ty * 256 - oy + MAP_TOP)));
      }
    }
    await Promise.all(jobs);
  }
  // trasy: zielone, z białą obwódką dla czytelności na mapie
  const toXY = (p) => [projX(p[1], z) - ox, projY(p[0], z) - oy + MAP_TOP];
  for (const [color, width] of [['#FFFFFF', 16], ['#16A34A', 9]]) {
    ctx.strokeStyle = color;
    ctx.lineWidth = width;
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    for (const t of S.trips) for (const seg of segmentsOf(t.points)) {
      ctx.beginPath();
      seg.forEach((p, i) => { const [x, y] = toXY(p); if (i) ctx.lineTo(x, y); else ctx.moveTo(x, y); });
      ctx.stroke();
    }
  }
  // początek i koniec dnia
  const first = S.trips[0].points[0], lastT = S.trips[S.trips.length - 1], last = lastT.points[lastT.points.length - 1];
  for (const [p, fill] of [[first, '#FFFFFF'], [last, '#111827']]) {
    const [x, y] = toXY(p);
    ctx.beginPath(); ctx.arc(x, y, 14, 0, Math.PI * 2);
    ctx.fillStyle = fill; ctx.fill();
    ctx.lineWidth = 6; ctx.strokeStyle = '#16A34A'; ctx.stroke();
  }
  ctx.restore();
  // stopka
  ctx.fillStyle = '#4B5563';
  ctx.font = '500 28px Inter, sans-serif';
  const towns = S.towns.length ? S.towns.slice(0, 4).join(', ') + (S.towns.length > 4 ? ` i ${S.towns.length - 4} więcej` : '') : '';
  ctx.fillText(towns, 60, MAP_TOP + MAP_H + 52, IMG_W - 120);
  ctx.font = '400 22px Inter, sans-serif';
  ctx.textAlign = 'right';
  ctx.fillText('Mapa © OpenStreetMap', IMG_W - 30, IMG_H - 24);
  ctx.textAlign = 'left';
}
function canvasBlob(canvas) {
  return new Promise((res, rej) => {
    try { canvas.toBlob((b) => (b ? res(b) : rej(new Error('pusty obraz'))), 'image/png'); } catch (e) { rej(e); }
  });
}

/* ---------------- Link do trasy (SMS): trasa zakodowana w samym linku ---------------- */
// Format: #s=v1!RRRR-MM-DD!metry!ms jazdy!nowe ulice!odcinek,odcinek,…  (odcinki: kodowanie „polyline”, dokładność 1e-5;
// „!” i „,” nie występują w alfabecie „polyline” (znaki 63–126), więc bezpiecznie oddzielają pola)
function encNum(v) {
  v = v < 0 ? ~(v << 1) : v << 1;
  let s = '';
  while (v >= 0x20) { s += String.fromCharCode((0x20 | (v & 0x1f)) + 63); v >>= 5; }
  return s + String.fromCharCode(v + 63);
}
function encPoly(pts) {
  let la0 = 0, lo0 = 0, out = '';
  for (const p of pts) {
    const la = Math.round(p[0] * 1e5), lo = Math.round(p[1] * 1e5);
    out += encNum(la - la0) + encNum(lo - lo0);
    la0 = la; lo0 = lo;
  }
  return out;
}
function decPoly(str) {
  const out = [];
  let i = 0, la = 0, lo = 0;
  while (i < str.length && out.length < 5000) {
    const vals = [];
    for (let k = 0; k < 2; k++) {
      let b, shift = 0, res = 0;
      do {
        if (i >= str.length) throw new Error('uszkodzony link');
        b = str.charCodeAt(i++) - 63;
        res |= (b & 0x1f) << shift;
        shift += 5;
      } while (b >= 0x20 && shift < 35);
      vals.push(res & 1 ? ~(res >> 1) : res >> 1);
    }
    la += vals[0]; lo += vals[1];
    out.push([la / 1e5, lo / 1e5]);
  }
  return out;
}
// upraszczanie linii (Douglas–Peucker) z tolerancją w metrach
function simplify(pts, tol) {
  if (pts.length < 3) return pts;
  const k = Math.cos((pts[0][0] * Math.PI) / 180) * 111320;
  const xy = pts.map((p) => [p[1] * k, p[0] * 110540]);
  const keep = new Uint8Array(pts.length);
  keep[0] = keep[pts.length - 1] = 1;
  const stack = [[0, pts.length - 1]];
  while (stack.length) {
    const [a, b] = stack.pop();
    let best = -1, dmax = tol;
    const [ax, ay] = xy[a], [bx, by] = xy[b];
    const dx = bx - ax, dy = by - ay, len = Math.hypot(dx, dy) || 1;
    for (let i = a + 1; i < b; i++) {
      const d = Math.abs(dy * xy[i][0] - dx * xy[i][1] + bx * ay - by * ax) / len;
      if (d > dmax) { dmax = d; best = i; }
    }
    if (best > 0) { keep[best] = 1; stack.push([a, best], [best, b]); }
  }
  return pts.filter((_, i) => keep[i]);
}
const MAX_LINK = 1800; // znaki linku — mieści się w kilku SMS-ach i w każdej przeglądarce
function shareLink(S) {
  const segs = S.trips.flatMap((t) => segmentsOf(t.points)).filter((s) => s.length > 1);
  const base = location.origin + location.pathname;
  let payload = '';
  for (const tol of [8, 15, 30, 60, 120, 250, 500]) {
    const enc = segs.map((s) => encPoly(simplify(s, tol))).join(',');
    payload = ['v1', S.key, Math.round(S.m), Math.round(S.ms), S.newCount, enc].join('!');
    if ((base + '#s=' + encodeURIComponent(payload)).length <= MAX_LINK) break;
  }
  return base + '#s=' + encodeURIComponent(payload);
}
function smsText(S) {
  return `Moje Drogi · ${dayLabel(S.key)}: ${fmtKm(S.m)}, ${S.trips.length} ${plural(S.trips.length, 'trasa', 'trasy', 'tras')}` +
    `${S.newCount ? `, ${S.newCount} ${plural(S.newCount, 'nowa ulica', 'nowe ulice', 'nowych ulic')}` : ''}.\nZobacz trasę na mapie: ${shareLink(S)}`;
}

/** Odczyt trasy z linku (dane z zewnątrz: sprawdzane i wyświetlane tylko jako tekst). */
function parseSharedHash(hash) {
  const m = /^#s=(.+)$/.exec(hash || '');
  if (!m) return null;
  try {
    const parts = decodeURIComponent(m[1]).split('!');
    if (parts[0] !== 'v1' || parts.length !== 6 || !/^\d{4}-\d{2}-\d{2}$/.test(parts[1])) return null;
    const segs = parts[5].split(',').filter(Boolean).slice(0, 200).map(decPoly)
      .map((s) => s.filter((p) => Math.abs(p[0]) <= 90 && Math.abs(p[1]) <= 180)).filter((s) => s.length > 1);
    if (!segs.length) return null;
    return { key: parts[1], m: Math.max(0, +parts[2] || 0), ms: Math.max(0, +parts[3] || 0), newCount: Math.max(0, +parts[4] || 0) | 0, segs };
  } catch {
    return null;
  }
}
let sharedLayer = null, sharedData = null;
// Trasa z linku pokazuje się wyłącznie w zakładce „Udostępnij” (własna mała mapa), nigdy na głównej mapie.
let recvMap = null;
function showSharedFromHash() {
  const d = parseSharedHash(location.hash);
  if (!d) return false;
  sharedData = d;
  showView('view-sharetab');
  $('#recv-card').hidden = false;
  $('#st-msg').textContent = '';
  $('#shared-info').textContent = `${dayLabel(d.key)}\n${fmtKm(d.m)}${d.ms ? ' · ' + fmtDur(d.ms) + ' jazdy' : ''}${d.newCount ? ` · ${d.newCount} ${plural(d.newCount, 'nowa ulica', 'nowe ulice', 'nowych ulic')}` : ''}`;
  $('#shared-save').hidden = !idb;
  if (!recvMap) {
    recvMap = L.map('recv-map', { preferCanvas: true, zoomControl: true, attributionControl: true });
    L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png', {
      maxZoom: 19, attribution: '&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a>',
    }).addTo(recvMap);
  }
  if (sharedLayer) sharedLayer.remove();
  sharedLayer = L.polyline(d.segs, { color: '#7C3AED', weight: 6, opacity: 0.95 }).addTo(recvMap);
  setTimeout(() => { recvMap.invalidateSize(); recvMap.fitBounds(sharedLayer.getBounds(), { padding: [20, 20], maxZoom: 16 }); }, 0);
  return true;
}
function closeShared() {
  if (sharedLayer) { sharedLayer.remove(); sharedLayer = null; }
  sharedData = null;
  $('#recv-card').hidden = true;
  try { history.replaceState(null, '', location.pathname); } catch { location.hash = ''; }
}
async function saveShared() {
  const d = sharedData;
  if (!d) return;
  const [y, mo, da] = d.key.split('-').map(Number);
  const start = new Date(y, mo - 1, da, 12).getTime();
  const points = [];
  d.segs.forEach((seg, i) => seg.forEach((p, j) => points.push(i > 0 && j === 0 ? [p[0], p[1], 0, 1] : [p[0], p[1], 0])));
  const t = { id: 's' + Date.now(), start, end: start + d.ms, source: 'gpx', points, recording: false, processed: false, km: trackLen(points), pausedMs: 0 };
  await dbPut('trips', t);
  state.trips.push(t);
  rebuild();
  closeShared();
  $('#st-msg').textContent = 'Zapisano otrzymaną trasę w Twoich trasach. Ulice rozpoznają się w tle.';
  processPending();
}

/* ---------------- Zakładka „Udostępnij”: dni z trasami ---------------- */
function renderShareTab() {
  const days = [...new Set(state.trips.filter((t) => !t.recording).map((t) => dayKey(t.start)))].sort().reverse();
  $('#st-empty').hidden = days.length > 0;
  const ul = $('#share-days');
  ul.replaceChildren();
  for (const key of days) {
    const trips = state.trips.filter((t) => !t.recording && dayKey(t.start) === key);
    const m = trips.reduce((x, t) => x + (t.km || 0), 0);
    const towns = [...new Set(trips.flatMap((t) => tripTowns(t)))];
    // link liczony dopiero przy stuknięciu (kodowanie trasy jest kosztowne przy wielu dniach)
    const sms = el('a', { class: 'a-sms', href: 'sms:', 'aria-label': `Wyślij SMS z trasami z dnia ${dayLabel(key)}` },
      svgIcon('M4 5h16v11H8l-4 4z M8 9h8 M8 12h5'), 'SMS');
    sms.addEventListener('click', () => { sms.href = 'sms:?&body=' + encodeURIComponent(smsText(daySummary(key))); });
    const wa = el('a', { class: 'a-wa', href: 'https://wa.me/', target: '_blank', rel: 'noopener', 'aria-label': `Wyślij przez WhatsApp trasy z dnia ${dayLabel(key)}` },
      svgIcon('M20 11.5a8 8 0 0 1-11.8 7L4 20l1.5-4.1A8 8 0 1 1 20 11.5z'), 'WhatsApp');
    wa.addEventListener('click', () => { wa.href = 'https://wa.me/?text=' + encodeURIComponent(smsText(daySummary(key))); });
    const more = el('button', { class: 'a-more', type: 'button', 'aria-label': `Więcej opcji udostępniania dnia ${dayLabel(key)}`, onclick: () => openShare(key) }, 'Więcej…');
    ul.append(el('li', { class: 'share-day' },
      el('div', {},
        el('b', {}, dayLabel(key)),
        el('div', { class: 'm' }, `${trips.length} ${plural(trips.length, 'trasa', 'trasy', 'tras')} · ${fmtKm(m)}${towns.length ? ' · ' + towns.slice(0, 3).join(', ') + (towns.length > 3 ? '…' : '') : ''}`)),
      el('div', { class: 'acts' }, sms, wa, more)));
  }
}

let shareCur = null;
async function openShare(key) {
  const S = daySummary(key);
  if (!S.trips.length) return;
  shareCur = { S, blob: null };
  $('#share-title').textContent = `Udostępnij: ${dayLabel(key)}`;
  $('#share-text').textContent = shareText(S);
  $('#share-sms').href = 'sms:?&body=' + encodeURIComponent(smsText(S));
  // WhatsApp: otwiera aplikację (albo WhatsApp Web) z gotowym tekstem; odbiorcę wybierasz w WhatsAppie
  $('#share-wa').href = 'https://wa.me/?text=' + encodeURIComponent(smsText(S));
  $('#share-hint').textContent = 'Przygotowuję obraz…';
  $('#share-go').disabled = true;
  $('#share-modal').hidden = false;
  $('#share-close').focus();
  const canvas = $('#share-canvas');
  await drawShareImage(canvas, S, true);
  try {
    shareCur.blob = await canvasBlob(canvas);
  } catch {
    // gdyby kafelki mapy zablokowały zapis obrazu: obraz bez podkładu mapy
    await drawShareImage(canvas, S, false);
    try { shareCur.blob = await canvasBlob(canvas); } catch { shareCur.blob = null; }
  }
  $('#share-go').disabled = false;
  $('#share-hint').textContent = shareCur.blob ? '' : 'Nie udało się przygotować obrazu. Możesz udostępnić sam opis.';
}
function closeShare() { $('#share-modal').hidden = true; shareCur = null; }

function downloadBlob(blob, name) {
  const a = el('a', { href: URL.createObjectURL(blob), download: name });
  document.body.append(a); a.click(); a.remove();
  setTimeout(() => URL.revokeObjectURL(a.href), 5000);
}
async function doShare() {
  if (!shareCur) return;
  const { S, blob } = shareCur;
  const text = shareText(S);
  const files = [];
  if (blob) files.push(new File([blob], `moje-drogi-${S.key}.png`, { type: 'image/png' }));
  if ($('#share-gpx').checked) files.push(new File([buildGpx(S)], `moje-drogi-${S.key}.gpx`, { type: 'application/gpx+xml' }));
  try {
    if (navigator.share && (!files.length || navigator.canShare?.({ files }))) {
      await navigator.share({ title: `Moje Drogi · ${dayLabel(S.key)}`, text, files });
      closeShare();
      setStatus('Udostępniono trasy z dnia.');
      return;
    }
  } catch (e) {
    if (e.name === 'AbortError') return; // anulowano w menu udostępniania
  }
  // bez menu udostępniania (np. komputer): zapisz pliki i skopiuj opis
  for (const f of files) downloadBlob(f, f.name);
  try { await navigator.clipboard.writeText(text); } catch {}
  $('#share-hint').textContent = 'Ta przeglądarka nie ma menu udostępniania. Zapisałem pliki, a opis skopiowałem do schowka.';
}

function svgIcon(d) {
  const ns = 'http://www.w3.org/2000/svg';
  const svg = document.createElementNS(ns, 'svg');
  svg.setAttribute('viewBox', '0 0 24 24');
  svg.setAttribute('aria-hidden', 'true');
  const path = document.createElementNS(ns, 'path');
  path.setAttribute('d', d);
  svg.append(path);
  return svg;
}

/* ---------------- Statystyki tygodniowe i miesięczne ---------------- */
const statState = { mode: 'week', sel: null };
const N_PERIODS = 12;
const MONTHS_SHORT = ['sty', 'lut', 'mar', 'kwi', 'maj', 'cze', 'lip', 'sie', 'wrz', 'paź', 'lis', 'gru'];
const MONTHS_FULL = ['styczeń', 'luty', 'marzec', 'kwiecień', 'maj', 'czerwiec', 'lipiec', 'sierpień', 'wrzesień', 'październik', 'listopad', 'grudzień'];

function periodStart(t, mode) {
  const d = new Date(t);
  if (mode === 'month') return new Date(d.getFullYear(), d.getMonth(), 1).getTime();
  const day = (d.getDay() + 6) % 7; // poniedziałek = 0
  return new Date(d.getFullYear(), d.getMonth(), d.getDate() - day).getTime();
}
function shiftPeriod(start, mode, k) {
  const d = new Date(start);
  return mode === 'month'
    ? new Date(d.getFullYear(), d.getMonth() + k, 1).getTime()
    : new Date(d.getFullYear(), d.getMonth(), d.getDate() + 7 * k).getTime();
}
function periodLabels(start, mode) {
  const d = new Date(start);
  if (mode === 'month') return { short: MONTHS_SHORT[d.getMonth()], full: `${MONTHS_FULL[d.getMonth()]} ${d.getFullYear()}` };
  const e = new Date(shiftPeriod(start, 'week', 1) - 86400000);
  const full = d.getMonth() === e.getMonth()
    ? `${d.getDate()}–${e.getDate()} ${MONTHS_SHORT[e.getMonth()]} ${e.getFullYear()}`
    : `${d.getDate()} ${MONTHS_SHORT[d.getMonth()]} – ${e.getDate()} ${MONTHS_SHORT[e.getMonth()]} ${e.getFullYear()}`;
  return { short: `${d.getDate()}.${String(d.getMonth() + 1).padStart(2, '0')}`, full };
}

/** Ostatnie 12 tygodni albo miesięcy: kilometry, liczba tras i nowe ulice (pierwszy raz przejechane). */
function periodStats(mode) {
  const cur = periodStart(Date.now(), mode);
  const periods = [];
  for (let k = N_PERIODS - 1; k >= 0; k--) {
    const start = shiftPeriod(cur, mode, -k);
    periods.push({ start, ...periodLabels(start, mode), m: 0, trips: 0, newStreets: 0, current: k === 0 });
  }
  const idx = new Map(periods.map((p, i) => [p.start, i]));
  const firstSeen = new Map();
  for (const t of [...state.trips].sort((a, b) => a.start - b.start)) {
    const i = idx.get(periodStart(t.start, mode));
    if (i != null) { periods[i].m += t.km || 0; periods[i].trips++; }
    for (const [town, sts] of Object.entries(t.streets || {})) {
      if (town === NO_TOWN) continue;
      for (const s of Object.keys(sts)) {
        if (s === NO_STREET) continue;
        const key = town + '|' + s;
        if (!firstSeen.has(key)) {
          firstSeen.set(key, true);
          if (i != null) periods[i].newStreets++;
        }
      }
    }
  }
  // najlepszy okres w całej historii (nie tylko w ostatnich 12)
  const all = new Map();
  for (const t of state.trips) { const k = periodStart(t.start, mode); all.set(k, (all.get(k) || 0) + (t.km || 0)); }
  let best = null;
  for (const [k, m] of all) if (!best || m > best.m) best = { start: k, m };
  return { periods, best };
}

function niceStep(max) {
  const raw = max / 4;
  const p = 10 ** Math.floor(Math.log10(raw));
  for (const f of [1, 2, 2.5, 5, 10]) if (f * p >= raw) return f * p;
  return 10 * p;
}
const kmNum = (m) => (m < 10000 ? nf1 : nf0).format(m / 1000);

function renderStats() {
  if (!$('#view-stats').classList.contains('active') && renderStats.done) return;
  renderStats.done = true;
  const mode = statState.mode;
  const week = mode === 'week';
  const { periods, best } = periodStats(mode);
  const cur = periods[periods.length - 1], prev = periods[periods.length - 2];
  const avg = periods.slice(0, -1).reduce((x, p) => x + p.m, 0) / (periods.length - 1);

  $('#per-week').setAttribute('aria-selected', String(week));
  $('#per-month').setAttribute('aria-selected', String(!week));
  $('#ps-cur').textContent = fmtKm(cur.m);
  $('#ps-cur-l').textContent = week ? 'ten tydzień' : 'ten miesiąc';
  $('#ps-prev').textContent = fmtKm(prev.m);
  $('#ps-prev-l').textContent = week ? 'poprzedni tydzień' : 'poprzedni miesiąc';
  $('#ps-avg').textContent = fmtKm(avg);
  $('#ps-avg-l').textContent = week ? 'średnio (11 pełnych tyg.)' : 'średnio (11 pełnych mies.)';
  const diff = cur.m - prev.m;
  $('#ps-delta').textContent = !cur.m && !prev.m ? ''
    : `${week ? 'W tym tygodniu' : 'W tym miesiącu'} ${diff >= 0 ? 'o ' + fmtKm(diff) + ' więcej' : 'o ' + fmtKm(-diff) + ' mniej'} niż ${week ? 'w poprzednim' : 'w poprzednim'}` +
      ` · ${cur.newStreets} ${plural(cur.newStreets, 'nowa ulica', 'nowe ulice', 'nowych ulic')}`;
  $('#ps-best').textContent = best ? fmtKm(best.m) : '0 km';
  $('#ps-best-l').textContent = best ? `najlepszy ${week ? 'tydzień' : 'miesiąc'}: ${periodLabels(best.start, mode).full}` : `najlepszy ${week ? 'tydzień' : 'miesiąc'}`;
  $('#ps-total').textContent = fmtKm(state.trips.reduce((x, t) => x + (t.km || 0), 0));
  $('#ps-longest').textContent = fmtKm(Math.max(0, ...state.trips.map((t) => t.km || 0)));
  $('#chart-title').textContent = week ? 'Kilometry w ostatnich 12 tygodniach' : 'Kilometry w ostatnich 12 miesiącach';
  $('#th-period').textContent = week ? 'Tydzień' : 'Miesiąc';

  // tabela (ta sama treść co wykres, bez najeżdżania)
  $('#chart-tbody').replaceChildren(...[...periods].reverse().map((p) =>
    el('tr', {}, el('td', {}, p.full + (p.current ? ' (trwa)' : '')), el('td', {}, kmNum(p.m)), el('td', {}, String(p.trips)), el('td', {}, String(p.newStreets)))));

  drawChart(periods);
}

function drawChart(periods) {
  const box = $('#chart');
  const W = Math.max(280, box.clientWidth || 340), H = 220;
  const padL = 34, padR = 6, padT = 22, padB = 26;
  const maxM = Math.max(...periods.map((p) => p.m));
  const maxKm = maxM / 1000;
  const step = maxKm > 0 ? niceStep(maxKm) : 1;
  const top = maxKm > 0 ? Math.ceil(maxKm / step) * step : 4;
  const y = (km) => padT + (H - padT - padB) * (1 - km / top);
  const band = (W - padL - padR) / periods.length;
  const bw = Math.min(24, band - 4);
  const ns = 'http://www.w3.org/2000/svg';
  const mk = (tag, attrs, text) => {
    const e = document.createElementNS(ns, tag);
    for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
    if (text != null) e.textContent = text;
    return e;
  };
  const svg = mk('svg', { viewBox: `0 0 ${W} ${H}`, role: 'img', 'aria-label': `Wykres słupkowy kilometrów, ${periods.length} okresów. Wartości są też w tabeli pod wykresem.` });
  for (let v = 0; v <= top + 1e-9; v += step) {
    const yy = y(v);
    svg.append(mk('line', { class: 'gridline', x1: padL, x2: W - padR, y1: yy, y2: yy }));
    svg.append(mk('text', { class: 'axis-t', x: padL - 6, y: yy + 4, 'text-anchor': 'end' }, nf1.format(v)));
  }
  // podpisy wartości tylko przy bieżącym okresie i maksimum
  const maxI = maxM > 0 ? periods.findIndex((p) => p.m === maxM) : -1;
  const showX = (i) => i === periods.length - 1 || (periods.length <= 12 && (W > 420 || i % 2 === (periods.length - 1) % 2));
  periods.forEach((p, i) => {
    const cx = padL + band * i + band / 2;
    const km = p.m / 1000;
    const g = mk('g', { class: 'col' + (statState.sel === i ? ' sel' : '') });
    if (km > 0) {
      const h = Math.max(2, y(0) - y(km)), x0 = cx - bw / 2, yTop = y(0) - h, r = Math.min(4, bw / 2, h);
      // zaokrąglona tylko góra słupka, podstawa prosta
      g.append(mk('path', { class: 'bar', d: `M${x0},${y(0)} V${yTop + r} Q${x0},${yTop} ${x0 + r},${yTop} H${x0 + bw - r} Q${x0 + bw},${yTop} ${x0 + bw},${yTop + r} V${y(0)} Z` }));
      if (i === periods.length - 1 || i === maxI) g.append(mk('text', { class: 'val-t', x: cx, y: yTop - 6, 'text-anchor': 'middle' }, kmNum(p.m)));
    } else {
      g.append(mk('rect', { class: 'zero', x: cx - bw / 2, y: y(0) - 1, width: bw, height: 1 }));
    }
    if (showX(i)) g.append(mk('text', { class: 'axis-t', x: cx, y: H - 8, 'text-anchor': 'middle' }, p.current ? (statState.mode === 'week' ? 'teraz' : p.short) : p.short));
    const label = `${p.full}${p.current ? ' (trwa)' : ''}: ${fmtKm(p.m)}, ${p.trips} ${plural(p.trips, 'trasa', 'trasy', 'tras')}, ${p.newStreets} ${plural(p.newStreets, 'nowa ulica', 'nowe ulice', 'nowych ulic')}`;
    const hit = mk('rect', { class: 'hit', x: padL + band * i, y: padT - 16, width: band, height: H - padT - padB + 16, tabindex: '0', role: 'button', 'aria-label': label });
    const show = () => showTip(p, i);
    hit.addEventListener('pointerenter', show);
    hit.addEventListener('focus', show);
    hit.addEventListener('click', show);
    g.append(hit);
    svg.append(g);
  });
  box.replaceChildren(svg);
  if (statState.sel != null && periods[statState.sel]) showTip(periods[statState.sel], statState.sel, true);
  else $('#chart-tip').hidden = true;
}

function showTip(p, i, quiet) {
  const tip = $('#chart-tip');
  tip.replaceChildren(
    el('b', {}, fmtKm(p.m)),
    el('span', {}, p.full + (p.current ? ' (trwa)' : '')),
    el('span', {}, `${p.trips} ${plural(p.trips, 'trasa', 'trasy', 'tras')} · ${p.newStreets} ${plural(p.newStreets, 'nowa ulica', 'nowe ulice', 'nowych ulic')}`));
  tip.hidden = false;
  if (!quiet && statState.sel !== i) {
    statState.sel = i;
    document.querySelectorAll('#chart .col').forEach((c, k) => c.classList.toggle('sel', k === i));
  }
}

/* ---------------- Tryb mapy: auto / ciemna / jasna ---------------- */
const MAP_THEMES = ['auto', 'dark', 'light'];
const THEME_NAMES = { auto: 'automatyczny (jak w telefonie)', dark: 'ciemny', light: 'jasny' };
const THEME_TAGS = { auto: 'Auto', dark: 'Ciemna', light: 'Jasna' };
const THEME_ICONS = {
  auto: '<circle cx="12" cy="12" r="8"/><path d="M12 4a8 8 0 0 0 0 16z" fill="currentColor"/>',
  dark: '<path d="M20 14.5A8 8 0 1 1 9.5 4a6.5 6.5 0 0 0 10.5 10.5z"/>',
  light: '<circle cx="12" cy="12" r="4"/><path d="M12 2v2M12 20v2M2 12h2M20 12h2M4.9 4.9l1.4 1.4M17.7 17.7l1.4 1.4M4.9 19.1l1.4-1.4M17.7 6.3l1.4-1.4"/>',
};
const systemDark = window.matchMedia ? window.matchMedia('(prefers-color-scheme: dark)') : null;
let mapTheme = 'auto';
try { mapTheme = MAP_THEMES.includes(localStorage.getItem('mapTheme')) ? localStorage.getItem('mapTheme') : 'auto'; } catch {}

function applyMapTheme() {
  const dark = mapTheme === 'dark' || (mapTheme === 'auto' && !!systemDark?.matches);
  document.body.classList.toggle('map-dark', dark);
  $('#theme-icon').innerHTML = THEME_ICONS[mapTheme];
  $('#theme-tag').textContent = THEME_TAGS[mapTheme];
  $('#btn-theme').setAttribute('aria-label', `Tryb mapy: ${THEME_NAMES[mapTheme]}. Stuknij, żeby zmienić.`);
}
function cycleMapTheme() {
  mapTheme = MAP_THEMES[(MAP_THEMES.indexOf(mapTheme) + 1) % MAP_THEMES.length];
  try { localStorage.setItem('mapTheme', mapTheme); } catch {}
  applyMapTheme();
  setStatus(`Mapa: tryb ${THEME_NAMES[mapTheme]}.`);
}
systemDark?.addEventListener?.('change', applyMapTheme);

function showView(id) {
  document.querySelectorAll('.view').forEach((v) => v.classList.toggle('active', v.id === id));
  // ekrany tras i szczegółów miejscowości należą do zakładki Miejscowości
  const tab = id === 'view-trips' || id === 'view-town' ? 'view-towns' : id;
  if (id !== 'view-map') document.body.classList.remove('map-full'); // inne ekrany zawsze z paskiem zakładek
  if (id === 'view-stats') setTimeout(renderStats, 0);
  document.querySelectorAll('.tabbar button').forEach((b) => b.classList.toggle('on', b.dataset.view === tab));
  if (id === 'view-map') setTimeout(() => map.invalidateSize(), 0);
  if (id === 'view-town') setTimeout(fitDistrictMap, 0);
}

/* ---------------- Import / eksport ---------------- */
async function importGpx(files) {
  let added = 0;
  for (const f of files) {
    const doc = new DOMParser().parseFromString(await f.text(), 'application/xml');
    const raw = [...doc.querySelectorAll('trkpt, rtept')].map((e) => [
      +e.getAttribute('lat'), +e.getAttribute('lon'),
      Date.parse(e.querySelector('time')?.textContent || '') || 0,
    ]).filter((p) => Number.isFinite(p[0]) && Number.isFinite(p[1]));
    const pts = [];
    for (const p of raw) if (!pts.length || dist(pts[pts.length - 1], p) >= MIN_STEP_M) pts.push(p);
    if (pts.length < 2) continue;
    const start = pts[0][2] || f.lastModified;
    const end = pts[pts.length - 1][2] || null;
    const t = { id: 'g' + start + '-' + Math.random().toString(36).slice(2, 7), start, end, points: pts, recording: false, processed: false, source: 'gpx', km: trackLen(pts) };
    await dbPut('trips', t);
    state.trips.push(t);
    added++;
  }
  drawTrips();
  setStatus(added ? `Zaimportowano ${added} ${plural(added, 'trasę', 'trasy', 'tras')}. Rozpoznaję ulice…` : 'W pliku nie znalazłem trasy.');
  showView('view-map');
  processPending();
}

async function exportBackup() {
  const data = { app: 'moje-drogi', v: 1, saved: new Date().toISOString(), trips: state.trips, towns: Object.values(state.townMeta) };
  const blob = new Blob([JSON.stringify(data)], { type: 'application/json' });
  const a = el('a', { href: URL.createObjectURL(blob), download: `moje-drogi-${new Date().toISOString().slice(0, 10)}.json` });
  document.body.append(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(a.href), 5000);
}

async function importBackup(file) {
  try {
    const data = JSON.parse(await file.text());
    if (data.app !== 'moje-drogi') throw new Error('zły plik');
    const have = new Set(state.trips.map((t) => t.id));
    let added = 0;
    for (const t of data.trips || []) if (!have.has(t.id)) { t.recording = false; await dbPut('trips', t); state.trips.push(t); added++; }
    for (const m of data.towns || []) { await dbPut('towns', m); state.townMeta[m.name] = m; }
    rebuild();
    setStatus(`Wczytano kopię: ${added} nowych tras.`);
    processPending();
  } catch {
    setStatus('To nie jest kopia zapasowa Moich Dróg.');
  }
}

/* ---------------- Start ---------------- */
async function init() {
  initMap();
  try { idb = await openDb(); }
  catch {
    setStatus('Przeglądarka nie pozwala zapisywać danych (tryb prywatny?).');
    showSharedFromHash(); // trasę z linku i tak pokaż (bez zapisu)
    return;
  }

  state.trips = await dbAll('trips');
  for (const m of await dbAll('towns')) state.townMeta[m.name] = m;
  // trasa przerwana zamknięciem aplikacji: zapisz ją jako zakończoną
  // wstrzymana trasa czeka na wznowienie także po zamknięciu aplikacji
  const pausedTrip = state.trips.filter((x) => x.recording && x.paused).sort((a, b) => b.start - a.start)[0];
  for (const t of state.trips.filter((x) => x.recording && x !== pausedTrip)) {
    t.recording = false;
    t.end = t.points.length ? t.points[t.points.length - 1][2] : t.start;
    t.km = trackLen(t.points);
    if (t.points.length < 3) { await dbDel('trips', t.id); } else await dbPut('trips', t);
  }
  state.trips = state.trips.filter((t) => t !== pausedTrip && (t.points.length >= 3 || t.source === 'gpx'));
  if (pausedTrip) {
    state.rec = pausedTrip;
    for (const seg of segmentsOf(pausedTrip.points)) L.polyline(seg, { color: '#EA580C', weight: 6, opacity: 0.6, interactive: false }).addTo(recPast);
    recTimer = setInterval(updateRecUi, 1000);
    updateRecUi();
    setStatus('Masz wstrzymaną trasę. Stuknij „Wznów”, żeby jechać dalej, albo „Zakończ”.');
  }
  // trasy rozpoznane starszą wersją przeliczamy jeszcze raz, żeby dostały podział na osiedla
  for (const t of state.trips) if (t.processed && t.v !== TRIP_V) t.processed = false;
  rebuild();
  const all = state.trips.flatMap((t) => t.points.map((p) => [p[0], p[1]]));
  // po starcie: śledzenie włączone — pierwszy odczyt GPS ustawi mapę na Tobie w stałym przybliżeniu
  // (do tego czasu widać Twoje trasy)
  if (all.length) map.fitBounds(L.latLngBounds(all), { padding: [30, 30], maxZoom: 15 });
  setFollow(true);
  showSharedFromHash(); // otwarte z linku: trasa w zakładce „Udostępnij”
  processPending();

  // pokaż pozycję bez nagrywania (jednorazowo)
  if (navigator.geolocation && window.isSecureContext) {
    navigator.geolocation.getCurrentPosition((p) => showPos(p.coords.latitude, p.coords.longitude, p.coords.accuracy), () => {}, { enableHighAccuracy: true, timeout: 15000 });
  }
}

$('#btn-rec').addEventListener('click', () => (state.rec ? stopRec() : startRec()));
$('#btn-pause').addEventListener('click', () => (state.rec?.paused ? resumeRec() : pauseRec()));
$('#btn-full').addEventListener('click', () => setFullMap(true));
$('#btn-full-exit').addEventListener('click', () => setFullMap(false));
$('#btn-full-follow').addEventListener('click', () => $('#btn-follow').click());
$('#btn-full-pause').addEventListener('click', () => (state.rec?.paused ? resumeRec() : pauseRec()));
document.addEventListener('keydown', (e) => {
  if (e.key === 'Escape' && document.body.classList.contains('map-full') && $('#share-modal').hidden) setFullMap(false);
});
$('#btn-layer').addEventListener('click', () => {
  state.showVisited = !state.showVisited;
  $('#btn-layer').classList.toggle('on', state.showVisited);
  $('#btn-layer').setAttribute('aria-pressed', String(state.showVisited));
  if (state.showVisited) visitedLayer.addTo(map); else visitedLayer.remove();
});
$('#btn-follow').addEventListener('click', () => {
  setFollow(!state.follow);
  if (state.follow && posMarker) map.setView(posMarker.getLatLng(), FOLLOW_ZOOM);
});
$('#sheet-details').addEventListener('click', () => {
  const T = sheetTown();
  if (T) openTown(T.name);
  else if (state.focus) setStatus(`W miejscowości ${state.focus.name} jeszcze nie jeździłeś.`);
  else showView('view-towns');
});

/* ---------------- Wyszukiwanie miejscowości ---------------- */
// Własne miejscowości podpowiadamy od razu; pozostałe szukamy w Nominatim dopiero po Enter
// (zasady Nominatim nie pozwalają na zapytania przy każdym naciśnięciu klawisza).
let focusMarker = null, searchCtl = null;
const qInput = $('#q'), resultsEl = $('#results');

function closeResults() { resultsEl.hidden = true; resultsEl.replaceChildren(); }

function resultButton(name, sub, tag, onPick) {
  const b = el('button', { type: 'button' },
    el('span', {}, el('span', { class: 'r-name' }, name), sub ? el('span', { class: 'r-sub' }, sub) : null),
    tag ? el('span', { class: 'r-tag' }, tag) : null);
  b.addEventListener('click', onPick);
  return el('li', {}, b);
}

function localMatches(q) {
  const f = norm(q);
  if (!f) return [];
  return Object.values(state.agg)
    .filter((T) => T.name !== NO_TOWN && norm(T.name).includes(f))
    .sort((a, b) => (norm(a.name).startsWith(f) ? 0 : 1) - (norm(b.name).startsWith(f) ? 0 : 1) || b.last - a.last)
    .slice(0, 6);
}

function renderResults(q, remote, info) {
  resultsEl.replaceChildren();
  const local = localMatches(q);
  const localNames = new Set(local.map((T) => T.name));
  for (const T of local) {
    const n = namedCount(T);
    resultsEl.append(resultButton(T.name, `${n} ${plural(n, 'ulica', 'ulice', 'ulic')} · ${fmtKm(T.m)}`, 'Twoja', () => pickLocal(T)));
  }
  for (const r of remote || []) {
    if (localNames.has(r.name)) continue;
    resultsEl.append(resultButton(r.name, r.sub, null, () => pickRemote(r)));
  }
  if (info) resultsEl.append(el('li', { class: 'r-info' }, info));
  else if (!local.length && !remote) resultsEl.append(el('li', { class: 'r-info' }, 'Naciśnij Enter, żeby wyszukać w promieniu 120 km.'));
  resultsEl.hidden = !resultsEl.children.length;
}

async function searchRemote(q) {
  searchCtl?.abort();
  searchCtl = new AbortController();
  renderResults(q, null, 'Szukam…');
  const dLat = RADIUS_KM / 111, dLon = RADIUS_KM / (111 * Math.cos(KRAKOW[0] * Math.PI / 180));
  const viewbox = [KRAKOW[1] - dLon, KRAKOW[0] + dLat, KRAKOW[1] + dLon, KRAKOW[0] - dLat].map((v) => v.toFixed(4)).join(',');
  const url = `https://nominatim.openstreetmap.org/search?format=jsonv2&addressdetails=1&limit=8&countrycodes=pl&featureType=settlement&accept-language=pl&bounded=1&viewbox=${viewbox}&q=${encodeURIComponent(q)}`;
  try {
    const r = await fetch(url, { signal: searchCtl.signal });
    if (!r.ok) throw new Error('nominatim ' + r.status);
    const list = (await r.json())
      .map((x) => {
        const a = x.address || {};
        const name = a.city || a.town || a.village || a.hamlet || x.name;
        const lat = +x.lat, lon = +x.lon;
        const km = Math.round(dist(KRAKOW, [lat, lon]) / 1000);
        return { name, lat, lon, bbox: x.boundingbox?.map(Number), sub: [a.municipality, a.county, `${km} km od Krakowa`].filter(Boolean).join(' · ') };
      })
      .filter((x) => x.name && !/^(gmina|powiat|województwo)\s/i.test(x.name) && dist(KRAKOW, [x.lat, x.lon]) <= RADIUS_KM * 1000);
    const seen = new Set();
    const uniq = list.filter((x) => { const k = x.name + x.sub; if (seen.has(k)) return false; seen.add(k); return true; });
    renderResults(q, uniq, uniq.length || localMatches(q).length ? null : 'Nie znalazłem takiej miejscowości w promieniu 120 km.');
  } catch (e) {
    if (e.name === 'AbortError') return;
    renderResults(q, [], 'Wyszukiwanie nie działa bez internetu.');
  }
}

function focusOn(name, lat, lon, bbox) {
  state.focus = { name, lat, lon };
  qInput.value = name;
  $('#q-clear').hidden = false;
  closeResults();
  qInput.blur();
  setFollow(false);
  if (!focusMarker) {
    focusMarker = L.circleMarker([lat, lon], { radius: 9, color: '#fff', weight: 3, fillColor: '#1D4ED8', fillOpacity: 1 }).addTo(map);
  } else focusMarker.setLatLng([lat, lon]);
  focusMarker.bindTooltip(name, { permanent: true, direction: 'top', offset: [0, -10] }).openTooltip();
  if (bbox && bbox.length === 4) map.fitBounds([[bbox[0], bbox[2]], [bbox[1], bbox[3]]], { padding: [30, 30], maxZoom: 15 });
  else map.setView([lat, lon], 14);
  renderSheet();
  if (!state.agg[name]) setStatus(`W miejscowości ${name} jeszcze nie jeździłeś.`);
  else setStatus('');
}

function pickLocal(T) {
  const pts = T.trips.flatMap((t) => t.points.map((p) => [p[0], p[1]]));
  const c = T.pt || pts[0];
  showView('view-map');
  focusOn(T.name, c[0], c[1], null);
  if (pts.length) map.fitBounds(L.latLngBounds(pts), { padding: [30, 30], maxZoom: 15 });
}
function pickRemote(r) { focusOn(r.name, r.lat, r.lon, r.bbox); }

function clearSearch() {
  searchCtl?.abort();
  state.focus = null;
  qInput.value = '';
  $('#q-clear').hidden = true;
  closeResults();
  if (focusMarker) { focusMarker.remove(); focusMarker = null; }
  setStatus('');
  renderSheet();
}

qInput.addEventListener('input', () => {
  $('#q-clear').hidden = !qInput.value;
  if (!qInput.value.trim()) { closeResults(); return; }
  renderResults(qInput.value, null, null);
});
qInput.addEventListener('focus', () => { if (qInput.value.trim() && !state.focus) renderResults(qInput.value, null, null); });
$('#search-form').addEventListener('submit', (e) => {
  e.preventDefault();
  const q = qInput.value.trim();
  if (q.length >= 2) searchRemote(q);
});
$('#q-clear').addEventListener('click', () => { clearSearch(); qInput.focus(); });
qInput.addEventListener('keydown', (e) => { if (e.key === 'Escape') closeResults(); });
document.addEventListener('pointerdown', (e) => { if (!e.target.closest('.search-wrap')) closeResults(); });
$('#town-filter').addEventListener('input', (e) => { state.filter = e.target.value; renderTowns(); });
$('#street-filter').addEventListener('input', (e) => { state.streetFilter = e.target.value; renderStreets(); });
$('#btn-csv').addEventListener('click', exportCsv);
document.querySelectorAll('.tabbar button').forEach((b) => b.addEventListener('click', () => showView(b.dataset.view)));
document.querySelectorAll('.pill').forEach((b) => b.addEventListener('click', () => {
  state.sort = b.dataset.sort;
  document.querySelectorAll('.pill').forEach((x) => x.classList.toggle('on', x === b));
  renderTowns();
}));
$('#btn-back').addEventListener('click', () => showView('view-towns'));
$('#btn-trips').addEventListener('click', () => showView('view-trips'));
$('#btn-theme').addEventListener('click', cycleMapTheme);
$('#share-close').addEventListener('click', closeShare);
$('#share-copy').addEventListener('click', async () => {
  if (!shareCur) return;
  const link = shareLink(shareCur.S);
  try { await navigator.clipboard.writeText(link); $('#share-hint').textContent = 'Link skopiowany. Wklej go w SMS albo innym komunikatorze.'; }
  catch { $('#share-hint').textContent = link; }
});
$('#shared-close').addEventListener('click', closeShared);
$('#shared-save').addEventListener('click', saveShared);
window.addEventListener('hashchange', showSharedFromHash);
$('#share-go').addEventListener('click', doShare);
$('#share-save').addEventListener('click', () => { if (shareCur?.blob) downloadBlob(shareCur.blob, `moje-drogi-${shareCur.S.key}.png`); });
$('#share-modal').addEventListener('click', (e) => { if (e.target.id === 'share-modal') closeShare(); });
document.addEventListener('keydown', (e) => { if (e.key === 'Escape' && !$('#share-modal').hidden) closeShare(); });
$('#btn-notify').addEventListener('click', toggleNotify);
$('#ns-close').addEventListener('click', () => { $('#ns-card').hidden = true; });
renderNotifySwitch();
applyMapTheme();
$('#per-week').addEventListener('click', () => { statState.mode = 'week'; statState.sel = null; renderStats(); });
$('#per-month').addEventListener('click', () => { statState.mode = 'month'; statState.sel = null; renderStats(); });
window.addEventListener('resize', () => { if ($('#view-stats').classList.contains('active')) renderStats(); });
$('#btn-trips-back').addEventListener('click', () => { tripSel.on = false; tripSel.ids.clear(); renderTrips(); showView('view-towns'); });
$('#btn-select').addEventListener('click', () => { tripSel.on = !tripSel.on; tripSel.ids.clear(); renderTrips(); });
$('#btn-sel-all').addEventListener('click', () => {
  for (const t of state.trips) if (!t.recording) tripSel.ids.add(t.id);
  renderTrips();
});
$('#btn-del-sel').addEventListener('click', () => {
  const n = tripSel.ids.size;
  if (n && confirm(`Usunąć ${n} ${plural(n, 'zaznaczoną trasę', 'zaznaczone trasy', 'zaznaczonych tras')}? Tego nie da się cofnąć.`)) {
    tripSel.on = false;
    deleteTrips([...tripSel.ids]);
  }
});
$('#btn-del-all').addEventListener('click', () => {
  const ids = state.trips.filter((t) => !t.recording).map((t) => t.id);
  if (ids.length && confirm(`Usunąć wszystkie trasy (${ids.length})? Znikną z mapy i ze statystyk. Tego nie da się cofnąć.`)) deleteTrips(ids);
});
$('#tab-streets').addEventListener('click', () => { state.detailTab = 'streets'; renderTown(); });
$('#tab-trips').addEventListener('click', () => { state.detailTab = 'trips'; renderTown(); });
$('#btn-show').addEventListener('click', () => fitTown(state.selected));
$('#btn-count').addEventListener('click', async () => {
  const btn = $('#btn-count');
  btn.disabled = true;
  btn.textContent = 'Liczę ulice…';
  try { await countStreets(state.selected); renderAll(); }
  catch (e) { console.warn(e); $('#d-area').textContent = 'Nie udało się pobrać listy ulic. Sprawdź internet i spróbuj za chwilę.'; btn.disabled = false; btn.textContent = 'Policz wszystkie ulice'; }
});
$('#in-gpx').addEventListener('change', (e) => { if (e.target.files.length) importGpx([...e.target.files]); e.target.value = ''; });
$('#in-backup').addEventListener('change', (e) => { if (e.target.files[0]) importBackup(e.target.files[0]); e.target.value = ''; });
$('#btn-export').addEventListener('click', exportBackup);
window.addEventListener('beforeunload', () => { if (state.rec) dbPut('trips', state.rec); });

if ('serviceWorker' in navigator && window.isSecureContext) navigator.serviceWorker.register('sw.js').catch(() => {});
init();
