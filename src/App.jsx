import initialData from '../data.json';
import React, { useState, useEffect, useRef, useCallback, useMemo, lazy, Suspense } from 'react';
import { createPortal } from 'react-dom';
import {
  ArrowUpRight, X, Smartphone, Tablet, Monitor, Search, Zap, Eye, Code, Globe,
  TrendingUp, Download, Star, MapPin, Phone, Mail, ExternalLink,
  LogOut, Save, Plus, Trash2, Lock, User, Shield, Upload,
  ChevronDown, ChevronUp, ChevronLeft, ChevronRight,
  ShoppingBag, HeartPulse, GraduationCap, Plane, Landmark, Cpu, Truck,
  Hotel, Car, Trophy, Home, UtensilsCrossed, Briefcase, Factory, Sun, Film, Sparkles, Palette,
  Award, Users, CheckCircle2, Headphones, Clock, Layers, Wallet, Rocket, BadgeCheck, Target, GripVertical, Menu as MenuIcon, MessageCircle
} from 'lucide-react';
const GravityModule = lazy(() => import('./components/ui/gravity').then(m => ({ default: m.Gravity })));
const MatterBodyModule = lazy(() => import('./components/ui/gravity').then(m => ({ default: m.MatterBody })));
const Ballpit = lazy(() => import('./components/ui/ballpit'));
const Gravity = (props) => <Suspense fallback={null}><GravityModule {...props} /></Suspense>;
const MatterBody = (props) => <Suspense fallback={null}><MatterBodyModule {...props} /></Suspense>;

// SHA-256 hash of the admin password. Stored hashed so the plaintext
// does not appear in the JS bundle. (Client-side auth is still not
// a real security boundary — this only raises the effort for casual inspection.)
const ADMIN_USER = 'admin';
const ADMIN_PASS_HASH = '627407089f6f560894f524b7a744f6e87fa2f8be27f0c5236270f4e941db9968';
const STORAGE_KEY = 'tp_site_v7';
const SESSION_KEY = 'tp_admin_session';
const LOCKOUT_KEY = 'tp_admin_lockout';
const MAX_ATTEMPTS = 5;
const LOCKOUT_MS = 15 * 60 * 1000;
const SESSION_MS = 30 * 60 * 1000;

// Pure-JS SHA-256 fallback for non-secure contexts (http:// + non-localhost),
// where `crypto.subtle` is undefined. Assumes input length fits in 32 bits of
// bits (always true for a <=128-char password).
function sha256JS(str) {
  const K = [0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2];
  const H = [0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19];
  const bytes = Array.from(new TextEncoder().encode(str));
  const bitLen = bytes.length * 8;
  bytes.push(0x80);
  while (bytes.length % 64 !== 56) bytes.push(0);
  bytes.push(0, 0, 0, 0); // upper 32 bits of 64-bit length (always 0 here)
  for (let i = 3; i >= 0; i--) bytes.push((bitLen >>> (i * 8)) & 0xff);
  const rotr = (n, x) => (x >>> n) | (x << (32 - n));
  for (let chunk = 0; chunk < bytes.length; chunk += 64) {
    const W = new Array(64);
    for (let t = 0; t < 16; t++) {
      W[t] = ((bytes[chunk+t*4]<<24) | (bytes[chunk+t*4+1]<<16) | (bytes[chunk+t*4+2]<<8) | bytes[chunk+t*4+3]) >>> 0;
    }
    for (let t = 16; t < 64; t++) {
      const s0 = rotr(7, W[t-15]) ^ rotr(18, W[t-15]) ^ (W[t-15] >>> 3);
      const s1 = rotr(17, W[t-2]) ^ rotr(19, W[t-2]) ^ (W[t-2] >>> 10);
      W[t] = (W[t-16] + s0 + W[t-7] + s1) >>> 0;
    }
    let [a,b,c,d,e,f,g,h] = H;
    for (let t = 0; t < 64; t++) {
      const S1 = rotr(6, e) ^ rotr(11, e) ^ rotr(25, e);
      const ch = (e & f) ^ (~e & g);
      const t1 = (h + S1 + ch + K[t] + W[t]) >>> 0;
      const S0 = rotr(2, a) ^ rotr(13, a) ^ rotr(22, a);
      const mj = (a & b) ^ (a & c) ^ (b & c);
      const t2 = (S0 + mj) >>> 0;
      h = g; g = f; f = e; e = (d + t1) >>> 0;
      d = c; c = b; b = a; a = (t1 + t2) >>> 0;
    }
    H[0]=(H[0]+a)>>>0; H[1]=(H[1]+b)>>>0; H[2]=(H[2]+c)>>>0; H[3]=(H[3]+d)>>>0;
    H[4]=(H[4]+e)>>>0; H[5]=(H[5]+f)>>>0; H[6]=(H[6]+g)>>>0; H[7]=(H[7]+h)>>>0;
  }
  return H.map(x => x.toString(16).padStart(8, '0')).join('');
}

async function sha256Hex(str) {
  if (typeof crypto !== 'undefined' && crypto.subtle) {
    try {
      const buf = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(str));
      return Array.from(new Uint8Array(buf)).map(b => b.toString(16).padStart(2, '0')).join('');
    } catch { /* fall through */ }
  }
  return sha256JS(str);
}

function readSession() {
  try {
    const raw = sessionStorage.getItem(SESSION_KEY);
    if (!raw) return null;
    const s = JSON.parse(raw);
    if (!s || !s.expires || Date.now() > s.expires) {
      sessionStorage.removeItem(SESSION_KEY);
      return null;
    }
    return s;
  } catch { return null; }
}

function writeSession() {
  sessionStorage.setItem(SESSION_KEY, JSON.stringify({ expires: Date.now() + SESSION_MS }));
}

function clearSession() { sessionStorage.removeItem(SESSION_KEY); }

function readLockout() {
  try {
    const raw = localStorage.getItem(LOCKOUT_KEY);
    if (!raw) return { attempts: 0, until: 0 };
    const l = JSON.parse(raw);
    if (l.until && Date.now() > l.until) {
      localStorage.removeItem(LOCKOUT_KEY);
      return { attempts: 0, until: 0 };
    }
    return l;
  } catch { return { attempts: 0, until: 0 }; }
}

function writeLockout(l) { localStorage.setItem(LOCKOUT_KEY, JSON.stringify(l)); }
function clearLockout() { localStorage.removeItem(LOCKOUT_KEY); }

const SITE_TYPES = ['Corporate','E-commerce','Healthcare','Restaurant','Real Estate','Industrial','Professional Services','NGO / Non-Profit','Solar Energy','Finance','Entertainment','Lifestyle','Brand Identity','SEO Campaign','Mobile App','Education','Hospitality','Technology','Other'];

const ST_COLORS = {
  'Corporate':'#1E40AF','E-commerce':'#7C3AED','Healthcare':'#059669','Restaurant':'#DC2626',
  'Real Estate':'#D97706','Industrial':'#475569','Professional Services':'#0369A1',
  'NGO / Non-Profit':'#D946EF','Solar Energy':'#CA8A04','Finance':'#1D4ED8',
  'Entertainment':'#DB2777','Lifestyle':'#EA580C','Brand Identity':'#7C3AED',
  'SEO Campaign':'#16A34A','Mobile App':'#2563EB','Education':'#0891B2',
  'Hospitality':'#BE123C','Technology':'#4F46E5','Other':'#64748B',
};

// ─── Browser / OS brand data ──────────────────────────────────────────────────
const _logo = (src) => <img src={src} width="18" height="18" alt="" style={{display:'block',flexShrink:0}}/>;
const COMPAT_META = {
  'Chrome':     { color:'#4285F4', bg:'#EBF3FE', svg:_logo('https://cdn.simpleicons.org/googlechrome/4285F4') },
  'Firefox':    { color:'#FF7139', bg:'#FFF3EE', svg:_logo('https://cdn.simpleicons.org/firefoxbrowser/FF7139') },
  'Safari':     { color:'#006CFF', bg:'#E5F1FF', svg:_logo('https://cdn.simpleicons.org/safari/006CFF') },
  'Edge':       { color:'#0078D4', bg:'#E5F4FF', svg:_logo('/icons/edge.png') },
  'Opera':      { color:'#FF1B2D', bg:'#FFE5E7', svg:_logo('https://cdn.simpleicons.org/opera/FF1B2D') },
  'Brave':      { color:'#FB542B', bg:'#FFF0EB', svg:_logo('https://cdn.simpleicons.org/brave/FB542B') },
  'Windows 11': { color:'#0067B8', bg:'#E5F0FF', svg:<svg viewBox="0 0 24 24" width="18" height="18" xmlns="http://www.w3.org/2000/svg"><path fill="#F25022" d="M1 1h10.5v10.5H1z"/><path fill="#7FBA00" d="M12.5 1H23v10.5H12.5z"/><path fill="#00A4EF" d="M1 12.5h10.5V23H1z"/><path fill="#FFB900" d="M12.5 12.5H23V23H12.5z"/></svg> },
  'Windows 10': { color:'#0067B8', bg:'#E5F0FF', svg:<svg viewBox="0 0 24 24" width="18" height="18" xmlns="http://www.w3.org/2000/svg"><path fill="#F25022" d="M1 1h10.5v10.5H1z"/><path fill="#7FBA00" d="M12.5 1H23v10.5H12.5z"/><path fill="#00A4EF" d="M1 12.5h10.5V23H1z"/><path fill="#FFB900" d="M12.5 12.5H23V23H12.5z"/></svg> },
  'macOS':      { color:'#1D1D1F', bg:'#F0F0F2', svg:<svg viewBox="0 0 24 24" width="18" height="18" xmlns="http://www.w3.org/2000/svg"><path fill="#1D1D1F" d="M18.71 19.5c-.83 1.24-1.71 2.45-3.05 2.47-1.34.03-1.77-.79-3.29-.79-1.53 0-2 .77-3.27.82-1.31.05-2.3-1.32-3.14-2.53C4.25 17 2.94 12.45 4.7 9.39c.87-1.52 2.43-2.48 4.12-2.51 1.28-.02 2.5.87 3.29.87.78 0 2.26-1.07 3.8-.91.65.03 2.47.26 3.64 1.98-.09.06-2.17 1.28-2.15 3.81.03 3.02 2.65 4.03 2.68 4.04-.03.07-.42 1.44-1.38 2.83M13 3.5c.73-.83 1.94-1.46 2.94-1.5.13 1.17-.34 2.35-1.04 3.19-.69.85-1.83 1.51-2.95 1.42-.15-1.15.41-2.35 1.05-3.11"/></svg> },
  'iOS':        { color:'#007AFF', bg:'#E5F2FF', svg:<svg viewBox="0 0 24 24" width="18" height="18" xmlns="http://www.w3.org/2000/svg"><path fill="#007AFF" d="M18.71 19.5c-.83 1.24-1.71 2.45-3.05 2.47-1.34.03-1.77-.79-3.29-.79-1.53 0-2 .77-3.27.82-1.31.05-2.3-1.32-3.14-2.53C4.25 17 2.94 12.45 4.7 9.39c.87-1.52 2.43-2.48 4.12-2.51 1.28-.02 2.5.87 3.29.87.78 0 2.26-1.07 3.8-.91.65.03 2.47.26 3.64 1.98-.09.06-2.17 1.28-2.15 3.81.03 3.02 2.65 4.03 2.68 4.04-.03.07-.42 1.44-1.38 2.83M13 3.5c.73-.83 1.94-1.46 2.94-1.5.13 1.17-.34 2.35-1.04 3.19-.69.85-1.83 1.51-2.95 1.42-.15-1.15.41-2.35 1.05-3.11"/></svg> },
  'Android':    { color:'#34A853', bg:'#E8FDF3', svg:<svg viewBox="0 0 24 24" width="18" height="18" xmlns="http://www.w3.org/2000/svg"><path fill="#34A853" d="M17.523 15.341a.868.868 0 1 1 0-1.736.868.868 0 0 1 0 1.736m-11.046 0a.868.868 0 1 1 0-1.736.868.868 0 0 1 0 1.736M17.8 10.08l1.742-3.017a.362.362 0 0 0-.627-.361l-1.765 3.056A10.514 10.514 0 0 0 12 9.015a10.514 10.514 0 0 0-5.15 1.737L5.085 7.696a.362.362 0 0 0-.627.361L6.2 10.08C3.88 11.464 2.25 13.9 2 16.784h20c-.25-2.884-1.88-5.32-4.2-6.704"/></svg> },
  'Linux':      { color:'#E8A800', bg:'#FFFBE5', svg:_logo('https://cdn.simpleicons.org/linux/E8A800') },
};

const DEFAULT_COMPAT = {
  browsers: [
    { name:'Chrome', status:'pass' }, { name:'Firefox', status:'pass' },
    { name:'Safari', status:'pass' }, { name:'Edge', status:'pass' }, { name:'Opera', status:'pass' },
  ],
  os: [
    { name:'Windows 11', status:'pass' }, { name:'macOS', status:'pass' },
    { name:'iOS', status:'pass' },        { name:'Android', status:'pass' },
  ],
};

const ALL_BROWSERS = ['Chrome','Firefox','Safari','Edge','Opera','Brave'];
const ALL_OS       = ['Windows 11','Windows 10','macOS','iOS','Android','Linux'];

const DEFAULT_METRICS = {
  performance: 95, accessibility: 98, bestPractices: 100, seo: 100,
  fcp: '0.9s', lcp: '1.5s', tbt: '80ms', cls: '0.02',
  responsive: { mobile: 96, tablet: 98, desktop: 100 },
  keywords: 0, backlinks: 0, organicTraffic: '—',
};

const DEFAULT_SECURITY = {
  grade: 'A+',
  score: 96,
  scannedOn: '2024',
  checks: [
    { name:'HTTPS / SSL Certificate',      status:'pass', detail:'TLS 1.3, valid cert' },
    { name:'HSTS (Strict Transport)',      status:'pass', detail:'max-age=63072000; preload' },
    { name:'Content-Security-Policy',      status:'pass', detail:'Strict CSP configured' },
    { name:'X-Frame-Options',              status:'pass', detail:'SAMEORIGIN' },
    { name:'X-Content-Type-Options',       status:'pass', detail:'nosniff' },
    { name:'Referrer-Policy',              status:'pass', detail:'strict-origin-when-cross-origin' },
    { name:'Mixed Content',                status:'pass', detail:'No insecure resources' },
    { name:'OWASP Top 10 Scan',            status:'pass', detail:'No critical findings' },
    { name:'Dependency Vulnerabilities',   status:'pass', detail:'0 high / 0 critical' },
    { name:'Admin Rate Limiting',          status:'pass', detail:'Brute-force protection' },
    { name:'Session Hardening',            status:'pass', detail:'HttpOnly · Secure · SameSite' },
    { name:'Cookie Flags',                 status:'pass', detail:'Secure + SameSite=Lax' },
  ],
};

const DEFAULT_DATA = initialData;

const isDataUrl = (v) => typeof v === 'string' && v.startsWith('data:');

// ─── Central Project Normalization & Multi-Platform Variant Expansion ────────
function normalizeProjects(rawList = []) {
  if (!Array.isArray(rawList)) return [];
  const result = [];
  const seenIds = new Set();

  for (const p of rawList) {
    if (!p) continue;

    // Expand multi-platform project variants (e.g. platforms: ['MacBook', 'Linux', 'Windows'])
    if (Array.isArray(p.platforms) && p.platforms.length > 1) {
      p.platforms.forEach((plat, idx) => {
        const platSlug = String(plat).toLowerCase().replace(/[^a-z0-9]/g, '');
        const clientName = p.client || p.name || p.title.replace(/\s+(App|Application|Website|Software|Tool|Client).*$/i, '');
        const typeLabel = p.type === 'app' ? 'App' : (p.type === 'tool' || p.type === 'software' ? 'Software' : 'Project');
        const displayTitle = `${clientName} — ${plat} ${typeLabel}`;
        const uniqueId = `${p.id}-${platSlug}`;

        let cleanUrl = (p.url || '').trim();
        if (cleanUrl.startsWith('//')) cleanUrl = 'https:' + cleanUrl;

        // Platform-specific images uploaded differently for this OS
        const platImages = (p.platformImages && Array.isArray(p.platformImages[plat]) && p.platformImages[plat].length > 0)
          ? p.platformImages[plat]
          : (p.images && p.images.length > 0 ? p.images : []);

        // Platform-specific data (challenge, solution, impact, tags, displayType, etc.)
        const platSpecific = (p.platformData && p.platformData[plat]) || {};

        if (!seenIds.has(uniqueId)) {
          seenIds.add(uniqueId);
          result.push({
            ...p,
            ...platSpecific,
            id: uniqueId,
            originalId: p.id,
            variantIndex: idx,
            platform: plat,
            displayTitle: displayTitle,
            title: displayTitle,
            name: clientName,
            images: platImages,
            url: cleanUrl,
            displayType: platSpecific.displayType || `${plat} ${typeLabel}`,
            categories: Array.from(new Set(['Apps', ...(p.categories || [])]))
          });
        }
      });
    } else {
      // Single project entry: detect/normalize platform
      let detectedPlatform = p.platform;
      if (!detectedPlatform) {
        const tLower = (p.title || '').toLowerCase();
        if (tLower.includes('macbook') || tLower.includes('macos')) detectedPlatform = 'MacBook';
        else if (tLower.includes('linux')) detectedPlatform = 'Linux';
        else if (tLower.includes('windows')) detectedPlatform = 'Windows';
        else if (tLower.includes('ios')) detectedPlatform = 'iOS';
        else if (tLower.includes('android')) detectedPlatform = 'Android';
        else if (p.type === 'app') detectedPlatform = 'Mobile (iOS & Android)';
        else if (p.type === 'website') detectedPlatform = 'Web';
        else if (p.type === 'tool' || p.type === 'software') detectedPlatform = 'Cloud Software';
        else if (p.type === 'logo') detectedPlatform = 'Brand Identity';
        else if (p.type === 'seo') detectedPlatform = 'Google Search';
      }

      let displayTitle = p.displayTitle || p.title;
      // Format clean title with em-dash if starting with client name, e.g. "Drivault — MacBook App"
      if (p.client && displayTitle.toLowerCase().startsWith(p.client.toLowerCase()) && !displayTitle.includes('—') && !displayTitle.includes(' - ')) {
        const rest = displayTitle.slice(p.client.length).trim().replace(/^[-–—:]\s*/, '');
        if (rest) displayTitle = `${p.client} — ${rest}`;
      }

      const cats = Array.isArray(p.categories) ? [...p.categories] : [];
      if (p.type === 'app' && !cats.includes('Apps')) cats.unshift('Apps');
      if (p.type === 'website' && !cats.includes('Websites')) cats.unshift('Websites');
      if ((p.type === 'tool' || p.type === 'software') && !cats.includes('Custom Software')) cats.unshift('Custom Software');

      let cleanUrl = (p.url || '').trim();
      if (cleanUrl.startsWith('//')) cleanUrl = 'https:' + cleanUrl;

      const entryId = String(p.id);
      if (!seenIds.has(entryId)) {
        seenIds.add(entryId);
        result.push({
          ...p,
          platform: detectedPlatform,
          displayTitle: displayTitle,
          title: displayTitle,
          name: p.client || p.title,
          url: cleanUrl,
          categories: cats
        });
      }
    }
  }
  return result;
}

function loadData() {
  try {
    const s = localStorage.getItem(STORAGE_KEY);
    let parsed = s ? JSON.parse(s) : null;
    if (!parsed || !Array.isArray(parsed.projects)) {
      return {
        ...DEFAULT_DATA,
        projects: normalizeProjects(DEFAULT_DATA.projects || [])
      };
    }

    // Automatically remove deprecated duplicate project entries (57 and 58 consolidated into 56)
    parsed.projects = (parsed.projects || []).filter(p => Number(p.id) !== 57 && Number(p.id) !== 58);

    // Merge any missing default projects
    const existingIds = new Set(parsed.projects.map(p => Number(p.id)));
    for (const dp of (DEFAULT_DATA.projects || [])) {
      if (!existingIds.has(Number(dp.id))) {
        parsed.projects.push(dp);
      } else if (Number(dp.id) === 56) {
        const localP56 = parsed.projects.find(p => Number(p.id) === 56);
        if (localP56) {
          localP56.title = dp.title;
          localP56.displayTitle = dp.displayTitle;
          localP56.platform = dp.platform;
          localP56.platforms = dp.platforms;
          localP56.platformImages = dp.platformImages;
          localP56.platformData = dp.platformData;
          localP56.displayType = dp.displayType;
          localP56.type = dp.type;
        }
      }
    }

    parsed.projects = normalizeProjects(parsed.projects.map(p => {
      const raw = p.images || (p.image ? [p.image] : []);
      return {
        ...p,
        images: raw.filter(u => u && !isDataUrl(u)),
        siteType: p.siteType || '',
      };
    }));

    if (isDataUrl(parsed.logo)) parsed.logo = '';
    if (typeof parsed.logo === 'string' && /techpenta\.com\/.*logo-black\.png/.test(parsed.logo)) {
      parsed.logo = '/logo-black.png';
    }
    if (!parsed.logo) parsed.logo = '/logo-black.png';
    return parsed;
  } catch {
    return {
      ...DEFAULT_DATA,
      projects: normalizeProjects(DEFAULT_DATA.projects || [])
    };
  }
}
function saveData(d) { localStorage.setItem(STORAGE_KEY, JSON.stringify(d)); }

async function fetchServerData() {
  try {
    const r = await fetch(`/api/data?t=${Date.now()}`, { cache: 'no-store' });
    if (!r.ok) return null;
    const ctype = r.headers.get('content-type') || '';
    if (!ctype.includes('application/json')) return null;
    const parsed = await r.json();
    if (!parsed || typeof parsed !== 'object') return null;
    // Guard: payload must look like a real dataset, not a stray test write
    if (!Array.isArray(parsed.projects) || !parsed.hero || typeof parsed.hero !== 'object') return null;
    if (parsed.projects) {
      parsed.projects = normalizeProjects(parsed.projects.map(p => {
        const raw = p.images || (p.image ? [p.image] : []);
        return { ...p, images: raw.filter(u => u && !isDataUrl(u)), siteType: p.siteType || '' };
      }));
    }
    if (isDataUrl(parsed.logo)) parsed.logo = '';
    return parsed;
  } catch { return null; }
}

async function pushServerData(d) {
  try {
    const r = await fetch('/api/data', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(d),
    });
    return r.ok;
  } catch { return false; }
}

function useReveal(options = {}) {
  const ref = useRef(null);
  const [visible, setVisible] = useState(false);
  const threshold = options.threshold !== undefined ? options.threshold : 0.08;
  const rootMargin = options.rootMargin || '0px 0px -40px 0px';

  useEffect(() => {
    const el = ref.current;
    if (!el) return;
    if (typeof IntersectionObserver === 'undefined') {
      setVisible(true);
      return;
    }
    const obs = new IntersectionObserver(([e]) => {
      if (e.isIntersecting) {
        setVisible(true);
        obs.disconnect();
      }
    }, { threshold, rootMargin });

    obs.observe(el);
    return () => { obs.disconnect(); };
  }, [threshold, rootMargin]);

  return [ref, visible];
}

// ─── CSS ──────────────────────────────────────────────────────────────────────
const CSS = `
@import url('https://fonts.googleapis.com/css2?family=Fraunces:opsz,wght,SOFT,WONK@9..144,300..900,0..100,0..1&family=Geist:wght@300;400;500;600;700&family=Geist+Mono:wght@400;500&display=swap');
*, *::before, *::after { box-sizing:border-box; margin:0; padding:0; }
html { scroll-behavior: smooth; }
body { font-family:'Geist',system-ui,sans-serif; background:#EFF6FF; color:#0F172A; }
.display { font-family:'Fraunces',serif; font-variation-settings:'opsz' 144,'SOFT' 50,'WONK' 1; line-height: 1.35; }
.display-it { font-family:'Fraunces',serif; font-style:italic; font-variation-settings:'opsz' 144,'SOFT' 100; line-height: 1.35; }
.mono { font-family:'Geist Mono',ui-monospace,monospace; }

@keyframes fadeUp { from{opacity:0;transform:translateY(32px)} to{opacity:1;transform:translateY(0)} }
@keyframes fadeIn { from{opacity:0} to{opacity:1} }
@keyframes float { 0%,100%{transform:translateY(0) rotate(0deg)} 50%{transform:translateY(-22px) rotate(8deg)} }
@keyframes floatAlt { 0%,100%{transform:translateY(0) rotate(0deg)} 50%{transform:translateY(18px) rotate(-6deg)} }
@keyframes marquee { from{transform:translateX(0)} to{transform:translateX(-50%)} }
@keyframes gradShift { 0%,100%{background-position:0% 50%} 50%{background-position:100% 50%} }
@keyframes pulseRing { 0%,100%{box-shadow:0 0 0 0 rgba(59,130,246,.45)} 50%{box-shadow:0 0 0 20px rgba(59,130,246,0)} }
@keyframes toastIn { from{opacity:0;transform:translateY(20px)} to{opacity:1;transform:translateY(0)} }
@keyframes spinCW { from{transform:rotate(0deg)} to{transform:rotate(360deg)} }
@keyframes loaderPop { 0%{opacity:0;transform:scale(.8)} 60%{opacity:1;transform:scale(1.04)} 100%{transform:scale(1)} }
@keyframes progressFill { from{width:0} to{width:100%} }
@keyframes slideLeft { from{opacity:0;transform:translateX(18px)} to{opacity:1;transform:translateX(0)} }
@keyframes slideRight2 { from{opacity:0;transform:translateX(-18px)} to{opacity:1;transform:translateX(0)} }
@keyframes zoomIn { 0%{opacity:0;transform:scale(.94)} 60%{opacity:1} 100%{opacity:1;transform:scale(1)} }
@keyframes barRise { 0%{transform:scaleY(.05);opacity:.35} 60%{opacity:1} 100%{transform:scaleY(1);opacity:1} }
@keyframes barPulse { 0%,100%{transform:scaleY(1)} 50%{transform:scaleY(1.06)} }
@keyframes trendDraw { 0%{stroke-dashoffset:260} 55%{stroke-dashoffset:0} 100%{stroke-dashoffset:0} }
@keyframes dotGlide { 0%{offset-distance:0%} 55%{offset-distance:100%} 100%{offset-distance:100%} }
@keyframes dotPulseGlow { 0%,100%{filter:drop-shadow(0 0 0 rgba(59,130,246,.0))} 50%{filter:drop-shadow(0 0 8px rgba(59,130,246,.8))} }
@keyframes sparkleIn { 0%{opacity:0;transform:scale(.4) rotate(0)} 40%{opacity:1} 100%{opacity:.9;transform:scale(1) rotate(90deg)} }
@keyframes baseShine { 0%{opacity:.25} 50%{opacity:.6} 100%{opacity:.25} }
.growth-icon .bar { transform-origin:bottom center; animation:barRise 1s cubic-bezier(.2,.8,.2,1) both, barPulse 3.2s ease-in-out infinite; }
.growth-icon .bar.b1 { animation-delay:0s, 1.2s; }
.growth-icon .bar.b2 { animation-delay:.15s, 1.4s; }
.growth-icon .bar.b3 { animation-delay:.3s, 1.6s; }
.growth-icon .bar.b4 { animation-delay:.45s, 1.8s; }
.growth-icon .trend { stroke-dasharray:260; stroke-dashoffset:260; animation:trendDraw 3.2s cubic-bezier(.2,.8,.2,1) infinite; }
.growth-icon .trend-dot { animation:dotGlide 3.2s cubic-bezier(.2,.8,.2,1) infinite, dotPulseGlow 1.6s ease-in-out infinite; offset-path:path('M8 64 L28 46 L48 34 L68 22 L88 10'); offset-rotate:0deg; }
.growth-icon .spark { transform-origin:center; animation:sparkleIn 2.2s ease-in-out infinite; }
.growth-icon .spark.s2 { animation-delay:.7s; }
.growth-icon .spark.s3 { animation-delay:1.4s; }
.growth-icon .base-glow { animation:baseShine 3.2s ease-in-out infinite; }

/* Industries */
@keyframes ringPulse { 0%,100%{transform:scale(1);opacity:.35} 50%{transform:scale(1.25);opacity:0} }
@keyframes iconFloat { 0%,100%{transform:translateY(0)} 50%{transform:translateY(-3px)} }
@keyframes dotDrift { 0%{transform:translate(0,0)} 50%{transform:translate(6px,-4px)} 100%{transform:translate(0,0)} }
.ind-card { position:relative; border-radius:18px; padding:22px 20px 18px; cursor:default; overflow:hidden; transition:transform .35s cubic-bezier(.2,.8,.2,1), box-shadow .35s, border-color .35s; isolation:isolate; }
.ind-card .ind-bg { position:absolute; inset:0; opacity:0; transition:opacity .4s; z-index:-1; }
.ind-card .ind-watermark { position:absolute; right:-8px; bottom:-22px; font-family:'Fraunces',serif; font-weight:600; font-style:italic; font-size:110px; line-height:1; letter-spacing:-.04em; opacity:.06; transition:opacity .35s, transform .5s, color .35s; pointer-events:none; z-index:0; user-select:none; }
.ind-card .ind-corner { position:absolute; top:0; right:0; width:62px; height:62px; transform:translate(32%,-32%) rotate(45deg); border-radius:4px; opacity:.14; transition:opacity .4s, transform .5s; z-index:0; }
.ind-card .ind-dots { position:absolute; bottom:14px; right:14px; width:52px; height:22px; opacity:.35; pointer-events:none; z-index:0; }
.ind-card .ind-badge { position:relative; width:44px; height:44px; border-radius:14px; display:flex; align-items:center; justify-content:center; transition:transform .35s cubic-bezier(.2,.8,.2,1), background .35s, border-color .35s; }
.ind-card .ind-ring { position:absolute; inset:-2px; border-radius:16px; border:1.5px solid currentColor; opacity:0; }
.ind-card:hover .ind-ring { animation:ringPulse 1.4s ease-out infinite; opacity:1; }
.ind-card:hover .ind-badge { animation:iconFloat 2.2s ease-in-out infinite; }
.ind-card:hover { transform:translateY(-7px) rotate(-.4deg); }
.ind-card:hover .ind-bg { opacity:1; }
.ind-card:hover .ind-watermark { opacity:.22; transform:translate(-4px,-4px); }
.ind-card:hover .ind-corner { opacity:.55; transform:translate(18%,-18%) rotate(45deg); }
.ind-card .ind-cta { display:flex; align-items:center; gap:6px; margin-top:14px; opacity:0; transform:translateY(6px); transition:opacity .3s, transform .3s; font-size:11px; font-family:'Geist Mono',monospace; text-transform:uppercase; letter-spacing:.12em; font-weight:600; }
.ind-card:hover .ind-cta { opacity:1; transform:translateY(0); }
.ind-card .ind-cta .cta-line { flex:1; height:1px; background:currentColor; opacity:.35; }

.ind-grid-bg { position:absolute; inset:0; background-image:radial-gradient(rgba(59,130,246,.14) 1px, transparent 1px); background-size:22px 22px; mask-image:radial-gradient(ellipse at center, #000 30%, transparent 75%); -webkit-mask-image:radial-gradient(ellipse at center, #000 30%, transparent 75%); pointer-events:none; opacity:.5; }

/* Tech pill clip-rect ripple — runs on hover/active/touch */
@keyframes pillClipRect {
  0%   { clip-path: inset(0 100% 0 0); opacity:0; }
  20%  { opacity:1; }
  50%  { clip-path: inset(0 0 0 0);    opacity:1; }
  80%  { opacity:1; }
  100% { clip-path: inset(0 0 0 100%); opacity:0; }
}
@keyframes pillPressPop {
  0%   { transform: scale(1); }
  35%  { transform: scale(1.14); }
  100% { transform: scale(1); }
}
@keyframes pillRingPulse {
  0%   { box-shadow: 0 0 0 0 rgba(255,255,255,.7), 0 8px 22px rgba(0,0,0,.18); }
  100% { box-shadow: 0 0 0 16px rgba(255,255,255,0), 0 8px 22px rgba(0,0,0,.18); }
}
.tech-pill { position:relative; overflow:hidden; transition:transform .25s cubic-bezier(.2,.8,.2,1), box-shadow .25s; will-change:transform; }
.tech-pill::before { content:''; position:absolute; inset:0; background:linear-gradient(100deg, rgba(255,255,255,0) 0%, rgba(255,255,255,.85) 45%, rgba(255,255,255,.95) 50%, rgba(255,255,255,.85) 55%, rgba(255,255,255,0) 100%); clip-path:inset(0 100% 0 0); opacity:0; pointer-events:none; }
.tech-pill:hover::before, .tech-pill:active::before, .tech-pill.is-touched::before { animation: pillClipRect 1s cubic-bezier(.4,.0,.2,1); }
.tech-pill:hover, .tech-pill:active, .tech-pill.is-touched { animation: pillPressPop .55s cubic-bezier(.2,.8,.2,1), pillRingPulse .9s ease-out; }

/* App project carousel wrapper */
.app-preview-wrap { background:#0F1D3E; }
@media (max-width: 640px) {
  .app-preview-wrap { max-height:none !important; }
}

/* App view stats (inside project modal) */
.app-stats-grid { display:grid; grid-template-columns:repeat(3,1fr); gap:10px; }
.app-stat-card { padding:18px; border-radius:12px; min-width:0; }
.app-stat-label { font-size:10px; text-transform:uppercase; margin-bottom:5px; letter-spacing:.08em; }
.app-stat-value { font-size:44px; line-height:1.05; word-break:break-word; overflow-wrap:anywhere; }
.app-stat-suffix { font-size:18px; }
.app-stat-sub { font-size:12px; margin-top:4px; }
@media (max-width: 640px) {
  .app-stats-grid { grid-template-columns:1fr 1fr; gap:8px; }
  .app-stat-card { padding:14px; }
  .app-stat-value { font-size:30px; }
  .app-stat-suffix { font-size:14px; }
  .app-view-intro { font-size:16px !important; margin-bottom:14px !important; line-height:1.4; }
}
@media (max-width: 380px) {
  .app-stats-grid { grid-template-columns:1fr; }
  .app-stat-value { font-size:34px; }
}

/* Contact section CTA buttons */
.contact-cta { display:inline-flex; align-items:center; gap:9px; padding:13px 22px; border-radius:99px; font-size:13px; font-weight:600; text-decoration:none; letter-spacing:.01em; transition:transform .25s cubic-bezier(.2,.8,.2,1), box-shadow .25s, background .25s, border-color .25s; white-space:nowrap; }
.contact-cta-primary { background:linear-gradient(135deg,#3B82F6,#1E40AF); color:#fff; box-shadow:0 10px 28px -8px rgba(59,130,246,.55); border:1px solid rgba(147,197,253,.35); }
.contact-cta-primary:hover { transform:translateY(-2px); box-shadow:0 16px 36px -8px rgba(59,130,246,.75); background:linear-gradient(135deg,#60A5FA,#2563EB); }
.contact-cta-ghost { background:rgba(255,255,255,.04); color:#DBEAFE; border:1px solid rgba(147,197,253,.25); }
.contact-cta-ghost:hover { transform:translateY(-2px); background:rgba(255,255,255,.09); border-color:rgba(147,197,253,.5); color:#fff; }
@media (max-width: 480px) {
  .contact-cta { padding:12px 18px; font-size:12.5px; }
}

@media (max-width: 860px) {
  #industries { padding:56px 5% 72px !important; }
  #industries .ind-header { gap:16px !important; margin-bottom:28px !important; }
  #industries .growth-icon { width:72px !important; height:72px !important; }
}
@media (max-width: 480px) {
  #industries { padding:44px 5% 60px !important; }
  #industries .growth-icon { width:60px !important; height:60px !important; }
}

/* Services */
@keyframes svcArrow { 0%{transform:translate(0,0) rotate(0)} 50%{transform:translate(4px,-4px) rotate(0)} 100%{transform:translate(0,0) rotate(0)} }
@keyframes svcBadgeSpin { 0%{transform:rotate(0) scale(1)} 50%{transform:rotate(-8deg) scale(1.08)} 100%{transform:rotate(0) scale(1)} }
.svc-row { position:relative; display:flex; align-items:center; gap:16px; padding:18px 20px 18px 16px; background:#fff; border:1px solid #E2E8F0; border-radius:14px; margin-bottom:10px; overflow:hidden; cursor:default; transition:transform .32s cubic-bezier(.2,.8,.2,1), border-color .32s, box-shadow .32s; }
.svc-row::before { content:''; position:absolute; left:0; top:0; bottom:0; width:4px; background:currentColor; transform:scaleY(.4); transform-origin:center; transition:transform .35s cubic-bezier(.2,.8,.2,1), width .35s; }
.svc-row::after { content:''; position:absolute; inset:0; background:linear-gradient(90deg, currentColor 0%, transparent 70%); opacity:0; transition:opacity .4s; pointer-events:none; z-index:0; mix-blend-mode:multiply; }
.svc-row:hover { transform:translateX(4px); border-color:currentColor; box-shadow:0 14px 36px -12px currentColor; }
.svc-row:hover::before { transform:scaleY(1); width:5px; }
.svc-row:hover::after { opacity:.08; }
.svc-row:hover .svc-badge { animation:svcBadgeSpin 1.4s ease-in-out infinite; border-color:currentColor; }
.svc-row:hover .svc-arrow { animation:svcArrow 1.2s ease-in-out infinite; background:currentColor !important; border-color:currentColor !important; }
.svc-row:hover .svc-arrow svg { stroke:#fff !important; color:#fff !important; }
.svc-badge { position:relative; width:52px; height:52px; border-radius:14px; display:flex; align-items:center; justify-content:center; flex-shrink:0; border:1.5px solid transparent; transition:border-color .32s; z-index:1; }
.svc-badge .svc-badge-num { position:absolute; top:-6px; right:-6px; min-width:20px; height:20px; padding:'0 6px'; border-radius:99px; background:#fff; border:1.5px solid currentColor; font-size:10px; font-family:'Geist Mono',monospace; font-weight:700; color:currentColor; display:flex; align-items:center; justify-content:center; letter-spacing:0; }
.svc-arrow { width:36px; height:36px; border-radius:50%; display:flex; align-items:center; justify-content:center; flex-shrink:0; border:1.5px solid currentColor; background:#fff; color:currentColor; transition:background .3s, color .3s, border-color .3s; }
.svc-arrow svg { stroke:currentColor; transition:stroke .2s; }

/* Tech stack chips */
.tech-chip { display:inline-flex; align-items:center; gap:8px; padding:8px 14px 8px 10px; background:#fff; border:1.5px solid #E2E8F0; border-radius:99px; font-size:12px; font-weight:600; color:#0F172A; transition:transform .25s cubic-bezier(.2,.8,.2,1), border-color .25s, box-shadow .25s, background .25s; cursor:default; }
.tech-chip:hover { transform:translateY(-3px) scale(1.04); }
.tech-chip img { width:18px; height:18px; display:block; flex-shrink:0; transition:transform .3s; }
.tech-chip:hover img { transform:rotate(-8deg) scale(1.08); }

/* Why Choose Us */
@keyframes whyBadgeFloat { 0%,100%{transform:translateY(0) rotate(0)} 50%{transform:translateY(-4px) rotate(-5deg)} }
@keyframes whyGlow { 0%,100%{opacity:.5; transform:scale(1)} 50%{opacity:.9; transform:scale(1.08)} }
@keyframes numSlide { from{transform:translateY(8px); opacity:0} to{transform:translateY(0); opacity:1} }
.why-card { position:relative; background:#fff; border:1px solid #E2E8F0; border-radius:18px; padding:22px 22px 20px; transition:transform .35s cubic-bezier(.2,.8,.2,1), border-color .35s, box-shadow .35s; overflow:hidden; cursor:default; isolation:isolate; }
.why-card::before { content:''; position:absolute; inset:0; background:var(--why-grad); opacity:0; transition:opacity .4s; z-index:-1; }
.why-card::after { content:''; position:absolute; top:-60px; right:-60px; width:140px; height:140px; border-radius:50%; background:var(--why-accent); opacity:0; filter:blur(30px); transition:opacity .5s; z-index:-1; }
.why-card:hover { transform:translateY(-6px); border-color:var(--why-accent); box-shadow:0 22px 50px -18px var(--why-accent-shadow); }
.why-card:hover::before { opacity:.55; }
.why-card:hover::after { opacity:.18; }
.why-card:hover .why-badge { animation:whyBadgeFloat 2s ease-in-out infinite; }
.why-card:hover .why-badge-glow { animation:whyGlow 1.6s ease-in-out infinite; }
.why-badge { position:relative; width:54px; height:54px; border-radius:16px; display:flex; align-items:center; justify-content:center; flex-shrink:0; background:var(--why-soft); border:1.5px solid var(--why-tint); transition:transform .35s; }
.why-badge-glow { position:absolute; inset:-4px; border-radius:20px; background:var(--why-accent); opacity:.25; filter:blur(10px); z-index:-1; }
.why-num { position:absolute; top:18px; right:22px; font-family:'Fraunces',serif; font-weight:600; font-style:italic; font-size:42px; line-height:1; color:var(--why-accent); opacity:.12; transition:opacity .35s, transform .4s; letter-spacing:-.03em; }
.why-card:hover .why-num { opacity:.9; transform:translateY(-2px); }
.why-arrow { position:absolute; bottom:20px; right:22px; width:28px; height:28px; border-radius:50%; background:var(--why-accent); color:#fff; display:flex; align-items:center; justify-content:center; opacity:0; transform:translate(-6px,6px); transition:opacity .3s, transform .3s; }
.why-arrow svg { stroke:#fff !important; color:#fff !important; }
.why-card:hover .why-arrow { opacity:1; transform:translate(0,0); }
.why-grid-bg { position:absolute; inset:0; background-image:linear-gradient(rgba(59,130,246,.07) 1px, transparent 1px), linear-gradient(90deg, rgba(59,130,246,.07) 1px, transparent 1px); background-size:40px 40px; mask-image:radial-gradient(ellipse at center, #000 20%, transparent 80%); -webkit-mask-image:radial-gradient(ellipse at center, #000 20%, transparent 80%); pointer-events:none; opacity:.6; }

/* Typewriter + active card */
@keyframes caretBlink { 0%,49%{opacity:1} 50%,100%{opacity:0} }
.type-caret { display:inline-block; width:4px; height:.88em; margin-left:4px; vertical-align:-2px; border-radius:2px; animation:caretBlink .95s steps(1) infinite; }
.why-card.active { transform:translateY(-6px); border-color:var(--why-accent); box-shadow:0 22px 50px -18px var(--why-accent-shadow), 0 0 0 2px var(--why-accent); }
.why-card.active::before { opacity:.55; }
.why-card.active::after { opacity:.18; }
.why-card.active .why-badge { animation:whyBadgeFloat 2s ease-in-out infinite; }
.why-card.active .why-badge-glow { animation:whyGlow 1.6s ease-in-out infinite; }
.why-card.active .why-num { opacity:.9; transform:translateY(-2px); }
.why-card.active .why-arrow { opacity:1; transform:translate(0,0); }

/* ── Responsive utilities ─────────────────────────────────────────── */
.resp-2col { display:grid; grid-template-columns:1fr 1fr; gap:60px; align-items:center; }
.resp-2to1 { display:grid; grid-template-columns:1fr 1fr; gap:20px; }
.resp-3col { display:grid; grid-template-columns:repeat(3,1fr); gap:10px; }
.resp-4col { display:grid; grid-template-columns:repeat(4,1fr); gap:10px; }
.resp-typewriter-chip { max-width:100%; }
.resp-typewriter-chip .tw-label { display:inline; }
.resp-typewriter-chip .tw-text { max-width:260px; }

@media (max-width: 980px) {
  .resp-2col { grid-template-columns:1fr; gap:36px; }
}
@media (max-width: 860px) {
  .resp-4col { grid-template-columns:repeat(2,1fr); }
  .resp-3col { grid-template-columns:repeat(2,1fr); }
  .ind-card { padding:18px 16px 14px; }
  .why-card { padding:18px 18px 16px; }
  .why-num { font-size:32px; top:14px; right:16px; }
  .svc-row { padding:14px 14px 14px 12px; gap:12px; }
  .svc-badge { width:46px; height:46px; border-radius:12px; }
  .svc-arrow { width:32px; height:32px; }
  .resp-typewriter-chip .tw-label { display:none; }
  .resp-typewriter-chip .tw-text { max-width:200px; font-size:14px !important; }
}
@media (max-width: 640px) {
  .resp-2to1 { grid-template-columns:1fr; }
  .resp-3col { grid-template-columns:1fr; }
  .resp-4col { grid-template-columns:repeat(2,1fr); }
  .resp-typewriter-chip .tw-text { max-width:160px; }
  .ind-card .ind-watermark { font-size:80px; bottom:-16px; right:-4px; }
  .device-shot-modal { width:100% !important; }
}
@media (max-width: 860px) {
  .modal-pad-head { padding:24px 24px 0 !important; }
  .modal-pad-body { padding:24px 24px 28px !important; }
}
@media (max-width: 640px) {
  .modal-pad-head { padding:20px 18px 0 !important; }
  .modal-pad-body { padding:20px 18px 24px !important; }
  .modal-pad-head h2 { font-size:clamp(1.35rem, 5.5vw, 1.9rem) !important; line-height:1.15 !important; }
  .modal-pad-head .modal-tagline { font-size:13.5px !important; padding-bottom:18px !important; line-height:1.5 !important; }
  .modal-pad-head .modal-meta-row { gap:6px !important; margin-bottom:10px !important; }
  .modal-pad-head .modal-meta-row .mono { font-size:10px !important; }
}
@media (max-width: 480px) {
  .resp-4col { grid-template-columns:1fr 1fr; gap:6px; }
  .resp-typewriter-chip { padding:8px 14px 8px 10px !important; gap:8px !important; }
  .resp-typewriter-chip .tw-text { max-width:140px; font-size:13px !important; }
  .modal-pad { padding:20px 18px !important; }
  .modal-pad-head { padding:18px 16px 0 !important; }
  .modal-pad-body { padding:18px 16px 22px !important; }
}

/* Prevent horizontal scroll caused by decorative blobs */
html, body, #root { overflow-x:hidden; max-width:100%; }

/* Freelancer Profile */
@keyframes flStarPop { 0%{transform:scale(.5) rotate(-20deg); opacity:0} 60%{transform:scale(1.2) rotate(5deg); opacity:1} 100%{transform:scale(1) rotate(0); opacity:1} }
@keyframes flPulseBorder { 0%,100%{box-shadow:0 0 0 0 rgba(41,178,254,.5)} 50%{box-shadow:0 0 0 14px rgba(41,178,254,0)} }
@keyframes flShine { 0%{background-position:-200% 0} 100%{background-position:200% 0} }
.fl-card { position:relative; background:linear-gradient(135deg,#0F1D3E 0%,#1E3A8A 50%,#0F1D3E 100%); border-radius:24px; padding:40px; color:#fff; overflow:hidden; isolation:isolate; }
.fl-card::before { content:''; position:absolute; inset:0; background:radial-gradient(circle at 15% 30%, rgba(41,178,254,.22) 0%, transparent 45%), radial-gradient(circle at 85% 80%, rgba(246,65,108,.15) 0%, transparent 45%); z-index:0; pointer-events:none; }
.fl-shine { position:absolute; inset:0; background:linear-gradient(90deg, transparent 30%, rgba(255,255,255,.05) 50%, transparent 70%); background-size:200% 100%; animation:flShine 6s linear infinite; pointer-events:none; z-index:0; }
.fl-avatar { position:relative; width:84px; height:84px; border-radius:50%; background:linear-gradient(135deg,#29B2FE,#1E40AF); display:flex; align-items:center; justify-content:center; font-family:'Fraunces',serif; font-weight:700; font-size:36px; color:#fff; flex-shrink:0; border:3px solid rgba(255,255,255,.2); animation:flPulseBorder 2.4s ease-in-out infinite; }
.fl-avatar::after { content:''; position:absolute; bottom:-2px; right:-2px; width:24px; height:24px; background:#22C55E; border-radius:50%; border:3px solid #0F1D3E; }
.fl-star { animation:flStarPop .6s cubic-bezier(.2,.8,.2,1) both; display:inline-block; }
.fl-stat-tile { position:relative; background:rgba(255,255,255,.06); backdrop-filter:blur(6px); border:1px solid rgba(255,255,255,.12); border-radius:16px; padding:18px; transition:transform .3s, background .3s, border-color .3s; }
.fl-stat-tile:hover { transform:translateY(-4px); background:rgba(255,255,255,.1); border-color:rgba(41,178,254,.5); }
.fl-badge { display:inline-flex; align-items:center; gap:7px; padding:6px 12px; border-radius:99px; font-size:11px; font-weight:700; text-transform:uppercase; letter-spacing:0.08em; white-space:nowrap; }
.fl-cta { display:inline-flex; align-items:center; gap:10px; padding:14px 28px; border-radius:99px; background:linear-gradient(135deg,#29B2FE,#0284C7); color:#fff; font-size:13px; font-weight:600; text-decoration:none; text-transform:uppercase; letter-spacing:0.1em; transition:transform .25s, box-shadow .25s; box-shadow:0 10px 30px -8px rgba(41,178,254,.55); border:none; }
.fl-cta:hover { transform:translateY(-2px); box-shadow:0 16px 40px -8px rgba(41,178,254,.75); }
@media (max-width: 860px) {
  .fl-card { padding:24px 20px; border-radius:18px; }
  .fl-avatar { width:68px; height:68px; font-size:28px; }
}
@media (max-width: 480px) {
  .fl-card { padding:20px 16px; }
}

/* Platform stat rows (compact horizontal layout) */
.fl-row-list { background:rgba(255,255,255,.04); border:1px solid rgba(255,255,255,.1); border-radius:14px; overflow:hidden; }
.fl-row { display:grid; grid-template-columns:auto 1fr auto auto; align-items:center; gap:14px; padding:12px 16px; border-bottom:1px solid rgba(255,255,255,.06); transition:background .25s; }
.fl-row:last-child { border-bottom:none; }
.fl-row:hover { background:rgba(255,255,255,.04); }
.fl-row-icon { width:30px; height:30px; border-radius:9px; display:flex; align-items:center; justify-content:center; flex-shrink:0; }
.fl-row-label { font-family:'Geist Mono',monospace; font-size:11px; text-transform:uppercase; letter-spacing:.08em; font-weight:500; }
.fl-row-value { font-family:'Fraunces',serif; font-size:22px; font-weight:600; color:#fff; line-height:1; display:flex; align-items:baseline; gap:4px; }
.fl-row-side { min-width:70px; display:flex; justify-content:flex-end; align-items:center; }
@media (max-width: 420px) {
  .fl-row { grid-template-columns:auto 1fr auto; padding:11px 12px; gap:10px; }
  .fl-row .fl-row-side { display:none; }
  .fl-row-value { font-size:19px; }
}

.anim-fadeUp  { animation:fadeUp .8s cubic-bezier(.2,.8,.2,1) both; }
.anim-fadeIn  { animation:fadeIn .55s ease both; }
.anim-float   { animation:float 6s ease-in-out infinite; }
.anim-floatAlt{ animation:floatAlt 7s ease-in-out infinite; }
.anim-marquee { animation:marquee 40s linear infinite; }
.anim-toast   { animation:toastIn .4s ease both; }
.anim-spin    { animation:spinCW 1s linear infinite; }

.delay-100{animation-delay:.1s} .delay-200{animation-delay:.2s} .delay-300{animation-delay:.3s}
.delay-400{animation-delay:.4s} .delay-500{animation-delay:.5s} .delay-600{animation-delay:.6s}

.reveal {
  opacity: 0;
  transform: translateY(42px) scale(0.98);
  filter: blur(4px);
  transition: opacity .8s cubic-bezier(.16,1,.3,1), transform .8s cubic-bezier(.16,1,.3,1), filter .8s cubic-bezier(.16,1,.3,1);
  will-change: transform, opacity, filter;
}
.reveal.in {
  opacity: 1;
  transform: none;
  filter: blur(0);
}

.reveal-pop {
  opacity: 0;
  transform: scale(0.93) translateY(36px);
  filter: blur(4px);
  transition: opacity .8s cubic-bezier(.16,1,.3,1), transform .8s cubic-bezier(.16,1,.3,1), filter .8s cubic-bezier(.16,1,.3,1);
  will-change: transform, opacity, filter;
}
.reveal-pop.in {
  opacity: 1;
  transform: none;
  filter: blur(0);
}

.reveal-slide-left {
  opacity: 0;
  transform: translateX(-45px);
  filter: blur(3px);
  transition: opacity .85s cubic-bezier(.16,1,.3,1), transform .85s cubic-bezier(.16,1,.3,1), filter .85s cubic-bezier(.16,1,.3,1);
  will-change: transform, opacity, filter;
}
.reveal-slide-left.in {
  opacity: 1;
  transform: none;
  filter: blur(0);
}

.reveal-slide-right {
  opacity: 0;
  transform: translateX(45px);
  filter: blur(3px);
  transition: opacity .85s cubic-bezier(.16,1,.3,1), transform .85s cubic-bezier(.16,1,.3,1), filter .85s cubic-bezier(.16,1,.3,1);
  will-change: transform, opacity, filter;
}
.reveal-slide-right.in {
  opacity: 1;
  transform: none;
  filter: blur(0);
}

/* Interactive Project Card Effects */
.project-card-interactive {
  position: relative;
  isolation: isolate;
  transition: transform .32s cubic-bezier(.16,1,.3,1), box-shadow .32s cubic-bezier(.16,1,.3,1), border-color .25s ease;
  will-change: transform, box-shadow;
}
.project-card-interactive:hover {
  transform: translateY(-8px) scale(1.006) !important;
  box-shadow: 0 22px 42px -10px rgba(30,64,175,.16), 0 0 0 1.5px rgba(59,130,246,.32) !important;
}
.project-card-shimmer::after {
  content: '';
  position: absolute;
  top: 0;
  left: -120%;
  width: 70%;
  height: 100%;
  background: linear-gradient(90deg, transparent, rgba(255,255,255,0.22), transparent);
  transform: skewX(-22deg);
  pointer-events: none;
  z-index: 10;
}
.project-card-interactive:hover.project-card-shimmer::after {
  left: 140%;
  transition: left 0.9s cubic-bezier(.16,1,.3,1);
}

/* Category Jump Dock */
.cat-jump-dock {
  position: sticky;
  top: 72px;
  z-index: 35;
  backdrop-filter: blur(16px);
  -webkit-backdrop-filter: blur(16px);
  background: rgba(255,255,255,0.92);
  border: 1.5px solid #DBEAFE;
  border-radius: 99px;
  padding: 6px 12px;
  box-shadow: 0 10px 30px rgba(30,64,175,0.08);
  display: flex;
  align-items: center;
  gap: 6px;
  overflow-x: auto;
  scrollbar-width: none;
  margin-bottom: 32px;
}
.cat-jump-dock::-webkit-scrollbar { display: none; }
.cat-dock-pill {
  display: inline-flex;
  align-items: center;
  gap: 6px;
  padding: 7px 13px;
  border-radius: 99px;
  font-size: 11px;
  font-weight: 600;
  cursor: pointer;
  white-space: nowrap;
  border: 1px solid transparent;
  transition: all .2s cubic-bezier(.16,1,.3,1);
}
.cat-dock-pill:hover {
  transform: translateY(-1px);
}
.cat-dock-pill.active {
  box-shadow: 0 4px 14px rgba(30,64,175,.25);
}

/* Category Section Header */
.cat-section-header {
  transition: transform .3s ease, box-shadow .3s ease;
}
.cat-section-header:hover {
  box-shadow: 0 12px 36px rgba(30,64,175,.08) !important;
}

/* Category Milestone Divider */
.cat-divider {
  display: flex;
  align-items: center;
  justify-content: center;
  margin: 54px 0 44px;
  position: relative;
}
.cat-divider::before {
  content: '';
  position: absolute;
  left: 0;
  right: 0;
  height: 1px;
  background: linear-gradient(90deg, transparent 0%, #DBEAFE 25%, #93C5FD 50%, #DBEAFE 75%, transparent 100%);
}
.cat-divider-node {
  position: relative;
  background: #FFFFFF;
  border: 1.5px solid #BFDBFE;
  padding: 6px 18px;
  border-radius: 99px;
  display: flex;
  align-items: center;
  gap: 8px;
  font-size: 10.5px;
  font-family: 'Geist Mono', monospace;
  color: #2563EB;
  text-transform: uppercase;
  letter-spacing: 0.12em;
  font-weight: 700;
  box-shadow: 0 4px 14px rgba(30,64,175,0.08);
}

.scrollbar-thin::-webkit-scrollbar{width:5px}
.scrollbar-thin::-webkit-scrollbar-thumb{background:rgba(59,130,246,.3);border-radius:4px}

.hero-bg { background:linear-gradient(135deg,#eff6ff 0%,#dbeafe 30%,#eff6ff 60%,#e0f2fe 100%); background-size:300% 300%; animation:gradShift 8s ease infinite; }
.blob { position:absolute; border-radius:50%; filter:blur(60px); opacity:.22; pointer-events:none; }
.card-hover { transition:transform .32s ease,box-shadow .32s ease,border-color .32s ease; }
.card-hover:hover { transform:translateY(-6px); box-shadow:0 18px 50px rgba(59,130,246,.18); border-color:rgba(59,130,246,.45)!important; }
.btn-primary { background:#1E40AF; color:#fff; border:none; cursor:pointer; transition:background .2s,transform .15s,box-shadow .2s; }
.btn-primary:hover { background:#1D4ED8; transform:translateY(-1px); box-shadow:0 8px 24px rgba(30,64,175,.35); }
.btn-outline { background:transparent; border:1.5px solid #1E40AF; color:#1E40AF; cursor:pointer; transition:all .2s; }
.btn-outline:hover { background:#1E40AF; color:#fff; }
.inp { border:1.5px solid #BFDBFE; border-radius:8px; padding:8px 12px; font-family:inherit; font-size:14px; width:100%; outline:none; transition:border-color .2s,box-shadow .2s; background:#fff; }
.inp:focus { border-color:#3B82F6; box-shadow:0 0 0 3px rgba(59,130,246,.14); }
.browser-bar { background:linear-gradient(180deg,#EFF6FF 0%,#DBEAFE 100%); }
.score-stroke { transition:stroke-dashoffset 1.4s cubic-bezier(.2,.8,.2,1); }

/* Carousel */
.carousel-btn { position:absolute; top:50%; transform:translateY(-50%); width:32px; height:32px; border-radius:50%; background:rgba(255,255,255,.92); border:none; cursor:pointer; display:flex; align-items:center; justify-content:center; color:#1E40AF; box-shadow:0 2px 8px rgba(0,0,0,.18); transition:background .2s,transform .2s; z-index:5; }
.carousel-btn:hover { background:#1E40AF; color:#fff; transform:translateY(-50%) scale(1.1); }
.carousel-dot { width:6px; height:6px; border-radius:50%; border:none; cursor:pointer; transition:background .25s,transform .25s; padding:0; }

/* Page fade-in after loader */
.page-enter { animation: fadeIn .6s ease both; }

/* Device shot modal */
@keyframes modalIn { from{opacity:0;transform:scale(.96)} to{opacity:1;transform:scale(1)} }
.device-shot-modal { animation: modalIn .25s cubic-bezier(.2,.8,.2,1) both; }
.shot-thumb { cursor:pointer; border-radius:6px; overflow:hidden; border:2px solid transparent; transition:border-color .15s,transform .15s; flex-shrink:0; }
.shot-thumb:hover,.shot-thumb.active { border-color:#2563EB; transform:scale(1.04); }
/* Device frames */
.frame-mobile { border:3px solid #1E3A8A; border-radius:18px; overflow:hidden; max-width:240px; margin:0 auto; box-shadow:0 8px 32px rgba(30,64,175,.25); }
.frame-tablet { border:3px solid #1E3A8A; border-radius:14px; overflow:hidden; max-width:380px; margin:0 auto; box-shadow:0 8px 32px rgba(30,64,175,.25); }
.frame-desktop { border:1px solid #DBEAFE; border-radius:10px; overflow:hidden; width:100%; box-shadow:0 8px 32px rgba(30,64,175,.15); }

/* Header / mobile nav */
.hamburger-btn { transition: background .15s, border-color .15s; }
.hamburger-btn:hover { background:#EFF6FF; border-color:#93C5FD; }
@media (max-width: 860px) {
  .nav-desktop { display:none !important; }
  .header-cta { display:none !important; }
  .hamburger-btn { display:inline-flex !important; }
}
@keyframes mobileMenuIn { from { opacity:0; transform:translateY(-8px); } to { opacity:1; transform:none; } }
.mobile-menu-panel { animation: mobileMenuIn .22s ease both; }

/* Hero 2-col banner */
.hero-banner { background:#EFF6FF; }
.hero-dots { background-image:radial-gradient(circle,#BFDBFE 1.2px,transparent 1.2px); background-size:22px 22px; }
@keyframes videoGlow { 0%,100%{box-shadow:0 0 0 0 rgba(59,130,246,.0)} 50%{box-shadow:0 8px 40px rgba(59,130,246,.22)} }
.video-wrap { animation:videoGlow 4s ease-in-out infinite; }
@keyframes bulletIn { from{opacity:0;transform:translateX(-12px)} to{opacity:1;transform:translateX(0)} }
.bullet-item { animation:bulletIn .5s ease both; }
`;


// ─── Loading Screen ───────────────────────────────────────────────────────────
function LoadingScreen({ onDone, logoUrl }) {
  const [fadeOut, setFadeOut] = useState(false);
  const [imgReady, setImgReady] = useState(false);
  useEffect(() => {
    const t1 = setTimeout(() => setFadeOut(true), 1400);
    const t2 = setTimeout(() => onDone(), 1900);
    return () => { clearTimeout(t1); clearTimeout(t2); };
  }, [onDone]);

  // Preload the logo. If it loads in time, we reveal it over the wordmark;
  // otherwise the wordmark keeps showing — never a blank space.
  useEffect(() => {
    if (!logoUrl) return;
    const img = new Image();
    img.onload = () => setImgReady(true);
    img.src = logoUrl;
  }, [logoUrl]);

  return (
    <div style={{ position:'fixed', inset:0, zIndex:9999, background:'#F0F7FF', display:'flex', flexDirection:'column', alignItems:'center', justifyContent:'center', gap:28, transition:'opacity .5s ease', opacity: fadeOut ? 0 : 1, pointerEvents: fadeOut ? 'none' : 'auto' }}>
      {/* Blobs */}
      <div className="blob anim-float" style={{ width:400, height:400, background:'#BFDBFE', top:-100, right:-80, opacity:.55 }} />
      <div className="blob anim-floatAlt" style={{ width:300, height:300, background:'#93C5FD', bottom:-80, left:-60, opacity:.45 }} />

      <div style={{ position:'relative', zIndex:1, textAlign:'center', animation:'loaderPop .6s cubic-bezier(.2,.8,.2,1) both' }}>
        {/* Logo — wordmark shows immediately, image fades in on top if it loads */}
        <div style={{ position:'relative', height:52, marginBottom:24, display:'flex', alignItems:'center', justifyContent:'center' }}>
          <div className="display" style={{ fontSize:32, fontWeight:800, color:'#0F1D3E', letterSpacing:'-0.02em', opacity: imgReady ? 0 : 1, transition:'opacity .35s ease' }}>
            Tech<span style={{ color:'#1E40AF' }}>penta</span>
          </div>
          {logoUrl && (
            <img
              src={logoUrl}
              alt="Techpenta"
              style={{ position:'absolute', height:52, maxWidth:220, objectFit:'contain', opacity: imgReady ? 1 : 0, transition:'opacity .35s ease' }}
            />
          )}
        </div>
        {/* Spinner ring */}
        <div style={{ position:'relative', width:56, height:56, margin:'0 auto 18px' }}>
          <svg width={56} height={56} style={{ position:'absolute', inset:0 }}>
            <circle cx={28} cy={28} r={22} stroke="rgba(30,64,175,.12)" strokeWidth={4} fill="none" />
          </svg>
          <svg width={56} height={56} className="anim-spin" style={{ position:'absolute', inset:0 }}>
            <circle cx={28} cy={28} r={22} stroke="#1E40AF" strokeWidth={4} fill="none" strokeLinecap="round" strokeDasharray="138" strokeDashoffset="100" />
          </svg>
        </div>
        <div className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.2em', color:'#1E40AF' }}>Loading Portfolio</div>
      </div>

      {/* Progress bar */}
      <div style={{ position:'absolute', bottom:0, left:0, right:0, height:3, background:'rgba(30,64,175,.08)' }}>
        <div style={{ height:'100%', background:'linear-gradient(90deg,#1E40AF,#60A5FA)', animation:'progressFill 1.4s cubic-bezier(.4,0,.2,1) forwards' }} />
      </div>
    </div>
  );
}

// ─── FadeImg — lazy-loads and fades in once decoded ──────────────────────────
function FadeImg({ style, onLoad, loading = 'lazy', decoding = 'async', ...rest }) {
  const [loaded, setLoaded] = useState(false);
  const ref = useRef(null);
  useEffect(() => {
    // If the image is already cached the browser may skip firing onLoad after
    // React attaches the ref — check .complete on mount and again on src change.
    if (ref.current && ref.current.complete && ref.current.naturalWidth > 0) {
      setLoaded(true);
    }
  }, [rest.src]);
  const baseTransition = 'opacity .5s ease';
  const mergedTransition = style?.transition ? `${baseTransition}, ${style.transition}` : baseTransition;
  return (
    <img
      ref={ref}
      loading={loading}
      decoding={decoding}
      {...rest}
      onLoad={(e) => { setLoaded(true); onLoad?.(e); }}
      style={{
        ...style,
        opacity: loaded ? (style?.opacity ?? 1) : 0,
        transition: mergedTransition,
      }}
    />
  );
}

// ─── Carousel ─────────────────────────────────────────────────────────────────
function Carousel({ images = [], aspectRatio = '65%', autoPlay = true, showNumber = false, fit = 'cover', onImageClick = null }) {
  const imgs = images.length ? images : [''];
  const [idx, setIdx] = useState(0);
  const [dir, setDir] = useState(null); // 'left' | 'right'
  const [animKey, setAnimKey] = useState(0);
  const [hovered, setHovered] = useState(false);
  const timer = useRef(null);
  const wrapRef = useRef(null);
  const swipedRef = useRef(false);
  const idxRef = useRef(idx);
  idxRef.current = idx;

  const go = useCallback((next, direction) => {
    setDir(direction);
    setAnimKey(k => k + 1);
    setIdx(next);
  }, []);

  const prev = (e) => { e?.stopPropagation(); go((idx - 1 + imgs.length) % imgs.length, 'right'); };
  const next = (e) => { e?.stopPropagation(); go((idx + 1) % imgs.length, 'left'); };

  useEffect(() => {
    const el = wrapRef.current;
    if (!el || imgs.length <= 1) return;
    let startX = 0, startY = 0, active = false, locked = false;

    const onStart = (e) => {
      const t = e.touches[0];
      startX = t.clientX; startY = t.clientY;
      active = true; locked = false;
      setHovered(true);
    };
    const onMove = (e) => {
      if (!active) return;
      const t = e.touches[0];
      const dx = t.clientX - startX;
      const dy = t.clientY - startY;
      if (!locked && (Math.abs(dx) > 8 || Math.abs(dy) > 8)) {
        locked = Math.abs(dx) > Math.abs(dy) ? 'x' : 'y';
      }
      if (locked === 'x') {
        e.preventDefault();
        e.stopPropagation();
      }
    };
    const onEnd = (e) => {
      if (!active) return;
      active = false;
      const t = e.changedTouches[0];
      const dx = t.clientX - startX;
      const dy = t.clientY - startY;
      if (Math.abs(dx) > 40 && Math.abs(dx) > Math.abs(dy)) {
        swipedRef.current = true;
        e.stopPropagation();
        e.preventDefault();
        if (dx < 0) go((idxRef.current + 1) % imgs.length, 'left');
        else go((idxRef.current - 1 + imgs.length) % imgs.length, 'right');
        setTimeout(() => { swipedRef.current = false; }, 400);
      }
      setTimeout(() => setHovered(false), 2500);
    };

    el.addEventListener('touchstart', onStart, { passive: true });
    el.addEventListener('touchmove', onMove, { passive: false });
    el.addEventListener('touchend', onEnd, { passive: false });
    el.addEventListener('touchcancel', onEnd, { passive: false });
    return () => {
      el.removeEventListener('touchstart', onStart);
      el.removeEventListener('touchmove', onMove);
      el.removeEventListener('touchend', onEnd);
      el.removeEventListener('touchcancel', onEnd);
    };
  }, [imgs.length, go]);

  const onClickCapture = (e) => {
    if (swipedRef.current) { e.stopPropagation(); e.preventDefault(); }
  };

  useEffect(() => {
    if (!autoPlay || imgs.length <= 1 || hovered) return;
    timer.current = setInterval(() => next(), 3200);
    return () => clearInterval(timer.current);
  }, [idx, hovered, imgs.length, autoPlay]);

  const isContain = fit === 'contain';
  const activeAnim = dir === 'left' ? 'slideLeft' : dir === 'right' ? 'slideRight2' : (isContain ? 'zoomIn' : 'fadeIn');

  return (
    <div ref={wrapRef}
      style={{
        position:'relative',
        paddingTop: aspectRatio,
        overflow:'hidden',
        background: isContain ? '#0B1220' : '#DBEAFE',
        touchAction: imgs.length > 1 ? 'pan-y' : 'auto',
        cursor: onImageClick ? 'pointer' : 'inherit'
      }}
      onMouseEnter={() => setHovered(true)}
      onMouseLeave={() => setHovered(false)}
      onClickCapture={onClickCapture}
      onClick={() => { if (onImageClick && !swipedRef.current) onImageClick(idx); }}
    >

      {/* Blurred backdrop — fills letterbox area when fit=contain */}
      {isContain && imgs[idx] && (
        <img key={`bg-${idx}`} src={imgs[idx]} alt="" aria-hidden="true"
          style={{
            position:'absolute', inset:0, width:'100%', height:'100%',
            objectFit:'cover', objectPosition:'center',
            filter:'blur(28px) saturate(1.1) brightness(.7)',
            transform:'scale(1.15)',
            zIndex:0,
            animation:'fadeIn .5s ease both',
          }}
        />
      )}

      {imgs.map((src, i) => (
        <img key={`${i}-${animKey}-${i === idx}`} src={src} alt="" loading="lazy"
          style={{
            position:'absolute', inset:0, width:'100%', height:'100%',
            objectFit: fit,
            objectPosition: isContain ? 'center' : 'top center',
            transition: i === idx ? 'none' : 'opacity .45s ease',
            opacity: i === idx ? 1 : 0,
            animation: i === idx ? `${activeAnim} .55s cubic-bezier(.22,1,.36,1) both` : 'none',
            zIndex: i === idx ? 2 : 1,
          }}
          onError={e => { e.target.style.opacity = '.25'; }}
        />
      ))}

      {/* Arrows — only if >1 image */}
      {imgs.length > 1 && hovered && (
        <>
          <button className="carousel-btn" onClick={prev} style={{ left:8 }}><ChevronLeft size={15} /></button>
          <button className="carousel-btn" onClick={next} style={{ right:8 }}><ChevronRight size={15} /></button>
        </>
      )}

      {/* Dots */}
      {imgs.length > 1 && (
        <div style={{ position:'absolute', bottom:8, left:'50%', transform:'translateX(-50%)', display:'flex', gap:5, zIndex:6 }}>
          {imgs.map((_, i) => (
            <button key={i} className="carousel-dot" onClick={e => { e.stopPropagation(); go(i, i > idx ? 'left' : 'right'); }}
              style={{ background: i === idx ? '#fff' : 'rgba(255,255,255,.45)', transform: i === idx ? 'scale(1.3)' : 'scale(1)' }} />
          ))}
        </div>
      )}

      {/* Counter badge */}
      {showNumber && imgs.length > 1 && (
        <div className="mono" style={{ position:'absolute', bottom:8, right:10, background:'rgba(0,0,0,.55)', color:'#fff', fontSize:10, padding:'3px 8px', borderRadius:99, zIndex:6, backdropFilter:'blur(4px)' }}>
          {idx+1}/{imgs.length}
        </div>
      )}
    </div>
  );
}

// ─── Root App ─────────────────────────────────────────────────────────────────
const getRoute = () => window.location.pathname.replace(/\/+$/, '').toLowerCase() === '/admin' ? 'admin' : 'portfolio';

export default function App() {
  const [loading, setLoading] = useState(true);
  const [route, setRoute] = useState(getRoute);
  const [authed, setAuthed] = useState(() => !!readSession());
  const [data, setData] = useState(loadData);
  const [toast, setToast] = useState(null);

  const showToast = (msg) => { setToast(msg); setTimeout(() => setToast(null), 3000); };
  const handleSave = useCallback(async (nd) => {
    setData(nd);
    saveData(nd);
    const ok = await pushServerData(nd);
    showToast(ok ? 'Changes saved — now live for everyone' : 'Saved locally (server unavailable)');
  }, []);

  const navigate = useCallback((path) => {
    if (window.location.pathname !== path) window.history.pushState({}, '', path);
    setRoute(getRoute());
  }, []);

  useEffect(() => {
    const onPop = () => setRoute(getRoute());
    window.addEventListener('popstate', onPop);
    return () => window.removeEventListener('popstate', onPop);
  }, []);

  const handleLogin = () => { writeSession(); setAuthed(true); };
  const handleLogout = useCallback(() => { clearSession(); setAuthed(false); navigate('/'); }, [navigate]);

  // Hydrate from server, then prune dead /projects/*.jpg references.
  useEffect(() => {
    let cancelled = false;
    (async () => {
      const server = await fetchServerData();
      let base = server || data;
      if (server && !cancelled) { setData(server); saveData(server); }

      const check = async (url) => {
        if (!url || typeof url !== 'string' || !url.startsWith('/projects/')) return true;
        try { const r = await fetch(url, { method: 'HEAD', cache: 'no-store' }); return r.ok; }
        catch { return true; }
      };
      const next = JSON.parse(JSON.stringify(base));
      let changed = false;
      for (const p of next.projects || []) {
        if (Array.isArray(p.images)) {
          const alive = [];
          for (const u of p.images) if (await check(u)) alive.push(u); else changed = true;
          p.images = alive;
        }
        if (p.responsiveShots && typeof p.responsiveShots === 'object') {
          for (const key of Object.keys(p.responsiveShots)) {
            const arr = p.responsiveShots[key];
            if (!Array.isArray(arr)) continue;
            const alive = [];
            for (const u of arr) if (await check(u)) alive.push(u); else changed = true;
            p.responsiveShots[key] = alive;
          }
        }
      }
      if (!cancelled && changed) { setData(next); saveData(next); }
    })();

    // Re-sync from server whenever the tab regains focus or visibility — ensures
    // deletions/edits made elsewhere land on the page without a full reload.
    // Admin edits live in AdminPanel's local state, so updating `data` here is safe.
    const resync = async () => {
      const fresh = await fetchServerData();
      if (fresh && !cancelled) { setData(fresh); saveData(fresh); }
    };
    const onFocus = () => { resync(); };
    const onVisible = () => { if (document.visibilityState === 'visible') resync(); };
    window.addEventListener('focus', onFocus);
    document.addEventListener('visibilitychange', onVisible);

    return () => {
      cancelled = true;
      window.removeEventListener('focus', onFocus);
      document.removeEventListener('visibilitychange', onVisible);
    };
    // run once on mount
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  // Auto-logout on session expiry and refresh on user activity.
  useEffect(() => {
    if (!authed) return;
    const check = () => { if (!readSession()) handleLogout(); };
    const refresh = () => { if (readSession()) writeSession(); };
    const tick = setInterval(check, 30000);
    const events = ['mousemove','keydown','click','scroll','touchstart'];
    events.forEach(ev => window.addEventListener(ev, refresh, { passive: true }));
    return () => {
      clearInterval(tick);
      events.forEach(ev => window.removeEventListener(ev, refresh));
    };
  }, [authed, handleLogout]);

  return (
    <>
      <style>{CSS}</style>
      {loading && <LoadingScreen onDone={() => setLoading(false)} logoUrl={data.logo} />}
      {!loading && (
        <div className="page-enter">
          {toast && (
            <div className="anim-toast mono" style={{ position:'fixed', bottom:28, right:28, zIndex:9999, background:'#1E40AF', color:'#fff', padding:'12px 22px', borderRadius:12, fontSize:13, boxShadow:'0 8px 32px rgba(30,64,175,.4)' }}>
              ✓ {toast}
            </div>
          )}
          {route === 'admin' && !authed && <AdminLogin onSuccess={handleLogin} onBack={() => navigate('/')} />}
          {route === 'admin' && authed && <AdminPanel data={data} onSave={handleSave} onLogout={handleLogout} />}
          {route === 'portfolio' && <Portfolio data={data} />}
        </div>
      )}
    </>
  );
}

// ─── Portfolio ────────────────────────────────────────────────────────────────
const TECH_FILTER_OPTIONS = [
  { id: 'all',          label: 'All Stacks',       icon: '✦' },
  { id: 'WordPress',    label: 'WordPress',        icon: '🌐' },
  { id: 'Shopify',      label: 'Shopify',          icon: '🛍️' },
  { id: 'Laravel',      label: 'Laravel',          icon: '🔴' },
  { id: 'React',        label: 'React',            icon: '⚛️' },
  { id: 'React Native', label: 'React Native',     icon: '📱' },
  { id: 'Next.js',      label: 'Next.js',          icon: '▲' },
  { id: 'Swift',        label: 'Swift / macOS',    icon: '' },
  { id: 'Rust',         label: 'Rust / Linux',     icon: '🦀' },
  { id: 'Windows',      label: 'C# / Windows',     icon: '⊞' },
  { id: 'SEO',          label: 'SEO',              icon: '📈' },
  { id: 'Logo Design',  label: 'Logo Design',      icon: '🎨' },
  { id: 'Responsive',   label: 'Responsive',       icon: '💻' },
  { id: 'MongoDB',      label: 'MongoDB',          icon: '🍃' },
  { id: 'PHP',          label: 'PHP',              icon: '🐘' },
  { id: 'GraphQL',      label: 'GraphQL',          icon: '◈' },
];

const projectMatchesTech = (p, techId) => {
  if (techId === 'all') return true;
  const tags = (p.tags || []).map(t => String(t).toLowerCase());
  const plat = (p.platform || '').toLowerCase();
  const title = (p.title || '').toLowerCase();
  const type = (p.type || '').toLowerCase();

  switch (techId) {
    case 'WordPress':
      return tags.some(t => t.includes('wordpress'));
    case 'Shopify':
      return tags.some(t => t.includes('shopify'));
    case 'Next.js':
      return tags.some(t => t.includes('next.js') || t.includes('nextjs'));
    case 'React':
      return tags.some(t => t === 'react' || t === 'react.js');
    case 'React Native':
      return tags.some(t => t.includes('react native'));
    case 'Laravel':
      return tags.some(t => t.includes('laravel'));
    case 'Swift':
      return tags.some(t => t.includes('swift')) || plat.includes('macbook') || plat.includes('macos') || title.includes('macbook') || title.includes('macos');
    case 'Rust':
      return tags.some(t => t.includes('rust')) || plat.includes('linux') || title.includes('linux');
    case 'Windows':
      return tags.some(t => t.includes('c#') || t.includes('.net') || t.includes('winui')) || plat.includes('windows') || title.includes('windows');
    case 'PHP':
      return tags.some(t => t === 'php');
    case 'MongoDB':
      return tags.some(t => t.includes('mongo'));
    case 'GraphQL':
      return tags.some(t => t.includes('graphql'));
    case 'SEO':
      return type === 'seo' || tags.some(t => t === 'seo' || t.includes('seo'));
    case 'Logo Design':
      return type === 'logo' || tags.some(t => t.includes('logo'));
    case 'Responsive':
      return tags.some(t => t === 'responsive');
    default:
      return tags.some(t => t.includes(techId.toLowerCase()));
  }
};

function Portfolio({ data }) {
  const [categoryFilter, setCategoryFilter] = useState('all');
  const [techFilter, setTechFilter] = useState('all');
  const [industryFilter, setIndustryFilter] = useState('all');
  const [searchQuery, setSearchQuery] = useState('');
  const [selected, setSelected] = useState(null);
  const [quoteOpen, setQuoteOpen] = useState(false);
  const [quoteContext, setQuoteContext] = useState(null);

  useEffect(() => {
    document.body.style.overflow = selected ? 'hidden' : '';
    return () => { document.body.style.overflow = ''; };
  }, [selected]);

  const projects = data.projects || [];

  // Available categories with human-readable labels, icons, descriptions & live counts
  const CATEGORY_DEFS = [
    { id: 'all',               label: 'All Projects',      icon: '✦',  desc: 'Complete portfolio of 50+ verified client deliverables' },
    { id: 'Apps',              label: 'Apps',              icon: '📱', desc: 'Desktop (macOS, Linux, Windows) & mobile (iOS, Android) applications' },
    { id: 'Websites',          label: 'Websites',          icon: '🌐', desc: 'Modern corporate websites, high-converting eCommerce & CMS' },
    { id: 'Software',          label: 'Software',          icon: '⚙️', desc: 'Custom enterprise software, cloud platforms & SaaS tools' },
    { id: 'Brand & Logo',      label: 'Brand & Logo',      icon: '🎨', desc: 'Memorable brand identities, vector logos & guidelines' },
    { id: 'SEO & Marketing',   label: 'SEO & Growth',      icon: '📈', desc: 'Local SEO, Google rankings & organic traffic growth' },
  ];

  // Helper to test if a project matches a category
  const projectMatchesCategory = (p, catId) => {
    if (!p) return false;
    if (catId === 'all') return true;
    if (catId === 'Apps') {
      return p.type === 'app';
    }
    if (catId === 'Websites') {
      return p.type === 'website';
    }
    if (catId === 'Software') {
      return p.type === 'tool' || p.type === 'software';
    }
    if (catId === 'Brand & Logo') {
      return p.type === 'logo';
    }
    if (catId === 'SEO & Marketing') {
      return p.type === 'seo';
    }
    return p.type === catId.toLowerCase();
  };

  const categories = useMemo(() => {
    return CATEGORY_DEFS.map(c => ({
      ...c,
      count: c.id === 'all' ? projects.length : projects.filter(p => projectMatchesCategory(p, c.id)).length
    }));
  }, [projects]);

  const techOptions = useMemo(() => {
    return TECH_FILTER_OPTIONS.map(t => ({
      ...t,
      count: t.id === 'all' ? projects.length : projects.filter(p => projectMatchesTech(p, t.id)).length
    }));
  }, [projects]);

  // Unique list of industries from all projects
  const industries = useMemo(() => {
    const s = new Set();
    for (const p of projects) {
      if (p.industry) s.add(p.industry);
      else if (p.siteType) s.add(p.siteType);
    }
    return ['all', ...Array.from(s).sort()];
  }, [projects]);

  // Filtered projects
  const filtered = useMemo(() => {
    let list = projects;

    // Category filter
    if (categoryFilter !== 'all') {
      list = list.filter(p => projectMatchesCategory(p, categoryFilter));
    }

    // Tech filter
    if (techFilter !== 'all') {
      list = list.filter(p => projectMatchesTech(p, techFilter));
    }

    // Industry filter
    if (industryFilter !== 'all') {
      list = list.filter(p => p.industry === industryFilter || p.siteType === industryFilter);
    }

    // Search query
    if (searchQuery.trim()) {
      const q = searchQuery.toLowerCase().trim();
      list = list.filter(p => {
        const matchTitle = (p.title || '').toLowerCase().includes(q);
        const matchClient = (p.client || '').toLowerCase().includes(q);
        const matchSummary = (p.businessSummary || p.tagline || '').toLowerCase().includes(q);
        const matchChallenge = (p.challenge || '').toLowerCase().includes(q);
        const matchSolution = (p.solution || '').toLowerCase().includes(q);
        const matchIndustry = (p.industry || p.siteType || '').toLowerCase().includes(q);
        const matchType = (p.displayType || p.type || '').toLowerCase().includes(q);
        const matchImpact = (p.impact || '').toLowerCase().includes(q);
        const matchTags = (p.tags || []).some(t => String(t).toLowerCase().includes(q));
        const matchFeatures = (p.keyFeatures || []).some(f => String(f).toLowerCase().includes(q));
        return matchTitle || matchClient || matchSummary || matchChallenge || matchSolution || matchIndustry || matchType || matchImpact || matchTags || matchFeatures;
      });
    }

    return list;
  }, [projects, categoryFilter, techFilter, industryFilter, searchQuery]);

  const handleOpenQuote = (project = null) => {
    setQuoteContext(project || null);
    setQuoteOpen(true);
  };

  return (
    <div style={{ minHeight:'100vh', background:'#F0F7FF', color:'#0F172A', overflowX:'hidden' }}>
      <Header data={data} onOpenQuote={() => handleOpenQuote()} />
      <HeroSection data={data} onOpenQuote={() => handleOpenQuote()} />
      <MarqueeSection items={data.marquee} />
      <WorkSection
        projects={projects}
        filtered={filtered}
        categories={categories}
        categoryFilter={categoryFilter}
        setCategoryFilter={setCategoryFilter}
        techFilter={techFilter}
        setTechFilter={setTechFilter}
        techOptions={techOptions}
        industryFilter={industryFilter}
        setIndustryFilter={setIndustryFilter}
        industries={industries}
        searchQuery={searchQuery}
        setSearchQuery={setSearchQuery}
        onSelect={setSelected}
        onOpenQuote={handleOpenQuote}
      />
      <ServicesSection data={data} />
      <WhyUsSection />
      <IndustriesSection data={data} />
      <PlatformsSection />
      <ContactSection data={data} />
      {selected && (
        <ProjectDetail
          project={selected}
          onClose={() => setSelected(null)}
          onOpenQuote={(p) => { setSelected(null); handleOpenQuote(p || selected); }}
        />
      )}
      <QuoteWizard
        open={quoteOpen}
        onClose={() => { setQuoteOpen(false); setQuoteContext(null); }}
        data={data}
        initialProject={quoteContext}
      />
    </div>
  );
}

// ─── Header ───────────────────────────────────────────────────────────────────
function Header({ data, onOpenQuote }) {
  const [menuOpen, setMenuOpen] = useState(false);
  const [headerH, setHeaderH] = useState(68);
  const headerRef = useRef(null);
  const close = () => setMenuOpen(false);

  useEffect(() => {
    if (!headerRef.current) return;
    const measure = () => headerRef.current && setHeaderH(headerRef.current.offsetHeight);
    measure();
    const ro = new ResizeObserver(measure);
    ro.observe(headerRef.current);
    window.addEventListener('resize', measure);
    return () => { ro.disconnect(); window.removeEventListener('resize', measure); };
  }, []);

  useEffect(() => {
    if (!menuOpen) return;
    const prev = document.body.style.overflow;
    document.body.style.overflow = 'hidden';
    const onKey = (e) => { if (e.key === 'Escape') setMenuOpen(false); };
    window.addEventListener('keydown', onKey);
    return () => { document.body.style.overflow = prev; window.removeEventListener('keydown', onKey); };
  }, [menuOpen]);

  const links = ['work','services','industries','contact'];

  return (
    <header ref={headerRef} style={{ position:'sticky', top:0, zIndex:30, background:'rgba(255,255,255,.92)', backdropFilter:'blur(16px)', borderBottom:'1px solid #DBEAFE', padding:'14px 5%', display:'flex', alignItems:'center', justifyContent:'space-between', gap:16 }}>
      <a href="#top" style={{ display:'flex', alignItems:'center', gap:12, textDecoration:'none', flexShrink:0 }}>
        <FadeImg src={data.logo} alt="Techpenta" loading="eager" fetchPriority="high" style={{ height:38, width:'auto' }} />
        <div style={{ lineHeight:1.4 }}>
          <div className="mono" style={{ fontSize:9, textTransform:'uppercase', letterSpacing:'0.12em', color:'#3B82F6' }}>e-Solutions Pvt. Ltd.</div>
          <div className="mono" style={{ fontSize:9, textTransform:'uppercase', letterSpacing:'0.12em', color:'#93C5FD' }}>Est. 2010 · Kolkata</div>
        </div>
      </a>
      <nav className="nav-desktop" style={{ display:'flex', alignItems:'center', gap:24 }}>
        {links.map(s => (
          <a key={s} href={`#${s}`} className="mono" style={{ textDecoration:'none', color:'#1E40AF', fontSize:11, textTransform:'uppercase', letterSpacing:'0.1em', transition:'color .2s' }}
            onMouseEnter={e => e.target.style.color='#3B82F6'} onMouseLeave={e => e.target.style.color='#1E40AF'}>{s}</a>
        ))}
      </nav>
      <div className="header-cta" style={{ display:'flex', gap:8 }}>
        <button type="button" onClick={() => onOpenQuote && onOpenQuote()} className="btn-primary mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.1em', padding:'8px 18px', borderRadius:99, border:'none', cursor:'pointer', display:'inline-block' }}>Get a Quote ↗</button>
      </div>
      <button className="hamburger-btn" aria-label={menuOpen ? 'Close menu' : 'Open menu'} aria-expanded={menuOpen} onClick={() => setMenuOpen(o => !o)}
        style={{ display:'none', background:'transparent', border:'1.5px solid #BFDBFE', borderRadius:10, padding:8, cursor:'pointer', color:'#1E40AF', alignItems:'center', justifyContent:'center' }}>
        {menuOpen ? <X size={22} /> : <MenuIcon size={22} />}
      </button>

      {menuOpen && (
        <>
          <div onClick={close} style={{ position:'fixed', left:0, right:0, bottom:0, top:headerH, background:'rgba(15,23,42,.35)', backdropFilter:'blur(4px)', zIndex:28 }} />
          <div className="mobile-menu-panel" role="dialog" aria-modal="true"
            style={{ position:'fixed', top:headerH, left:0, right:0, zIndex:29, background:'#fff', borderBottom:'1px solid #DBEAFE', boxShadow:'0 16px 40px rgba(30,64,175,.12)', padding:'14px 5% 22px', display:'flex', flexDirection:'column', gap:6 }}>
            {links.map(s => (
              <a key={s} href={`#${s}`} onClick={close} className="mono"
                style={{ display:'block', padding:'14px 4px', textDecoration:'none', color:'#1E40AF', fontSize:13, textTransform:'uppercase', letterSpacing:'0.12em', borderBottom:'1px solid #EFF6FF' }}>{s}</a>
            ))}
            <button type="button" onClick={() => { close(); onOpenQuote && onOpenQuote(); }} className="btn-primary mono"
              style={{ marginTop:12, textAlign:'center', fontSize:12, textTransform:'uppercase', letterSpacing:'0.12em', padding:'12px 18px', borderRadius:99, border:'none', cursor:'pointer' }}>Get a Quote ↗</button>
          </div>
        </>
      )}
    </header>
  );
}

// ─── Hero ─────────────────────────────────────────────────────────────────────
// ─── Video embed helper ───────────────────────────────────────────────────────
function parseVideo(url) {
  if (!url || !url.trim()) return null;
  const yt = url.match(/(?:youtube\.com\/(?:watch\?v=|embed\/)|youtu\.be\/)([a-zA-Z0-9_-]{11})/);
  if (yt) return { type:'youtube', src:`https://www.youtube.com/embed/${yt[1]}?rel=0&modestbranding=1` };
  const vm = url.match(/vimeo\.com\/(\d+)/);
  if (vm) return { type:'vimeo', src:`https://player.vimeo.com/video/${vm[1]}?color=3b82f6` };
  if (/\.(mp4|webm|ogg)(\?|$)/i.test(url)) return { type:'video', src:url };
  return { type:'iframe', src:url };
}

function VideoPlayer({ url, quote, poster }) {
  const [playing, setPlaying] = useState(false);
  const [started, setStarted] = useState(false);
  const videoRef = useRef(null);
  const parsed = parseVideo(url);
  // Append #t=0.1 so browsers without a poster still render the first frame as a still.
  const nativeSrc = parsed && parsed.type === 'video'
    ? (parsed.src.includes('#') ? parsed.src : `${parsed.src}#t=0.1`)
    : null;

  const handleNativePlay = () => {
    if (videoRef.current) {
      if (playing) { videoRef.current.pause(); setPlaying(false); }
      else { videoRef.current.play(); setPlaying(true); setStarted(true); }
    }
  };

  return (
    <div>
      {/* Quote above video */}
      {quote && (
        <p className="anim-fadeUp delay-200" style={{ fontSize:'clamp(1rem,1.8vw,1.25rem)', fontWeight:700, color:'#0F172A', lineHeight:1.4, marginBottom:20, textAlign:'center' }}>
          {quote}
        </p>
      )}

      {/* Dotted bg + video card */}
      <div className="hero-dots" style={{ borderRadius:16, padding:18, background:'#EFF6FF' }}>
        <div className="video-wrap" style={{ borderRadius:12, overflow:'hidden', background:'#1E3A8A', position:'relative', aspectRatio:'16/9' }}>

          {/* YouTube / Vimeo / iframe embed */}
          {parsed && (parsed.type === 'youtube' || parsed.type === 'vimeo' || parsed.type === 'iframe') && (
            <iframe src={parsed.src} title="Intro video" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture" allowFullScreen
              style={{ position:'absolute', inset:0, width:'100%', height:'100%', border:'none' }} />
          )}

          {/* Native HTML5 video */}
          {parsed && parsed.type === 'video' && (
            <>
              {poster && !started && (
                <FadeImg src={poster} alt="Video thumbnail" style={{ position:'absolute', inset:0, width:'100%', height:'100%', objectFit:'cover', zIndex:1, pointerEvents:'none' }} />
              )}
              <video ref={videoRef} src={nativeSrc} poster={poster || undefined} preload="metadata"
                style={{ position:'absolute', inset:0, width:'100%', height:'100%', objectFit:'cover' }}
                onPlay={() => { setPlaying(true); setStarted(true); }}
                onPause={() => setPlaying(false)}
                onEnded={() => {
                  setPlaying(false);
                  setStarted(false);
                  if (videoRef.current) videoRef.current.currentTime = 0;
                }} />
              {!playing && (
                <button onClick={handleNativePlay}
                  style={{ position:'absolute', inset:0, width:'100%', height:'100%', background:'rgba(15,23,42,.35)', border:'none', cursor:'pointer', display:'flex', alignItems:'center', justifyContent:'center' }}>
                  <div style={{ width:64, height:64, borderRadius:'50%', background:'#2563EB', display:'flex', alignItems:'center', justifyContent:'center', boxShadow:'0 8px 32px rgba(37,99,235,.5)', transition:'transform .2s' }}
                    onMouseEnter={e=>e.currentTarget.style.transform='scale(1.12)'} onMouseLeave={e=>e.currentTarget.style.transform='scale(1)'}>
                    <svg width={22} height={22} viewBox="0 0 24 24" fill="#fff"><polygon points="5,3 19,12 5,21"/></svg>
                  </div>
                </button>
              )}
            </>
          )}

          {/* No video — placeholder */}
          {!parsed && (
            <div style={{ position:'absolute', inset:0, display:'flex', flexDirection:'column', alignItems:'center', justifyContent:'center', gap:14, background:'linear-gradient(135deg,#1E3A8A,#1E40AF)' }}>
              <div style={{ width:64, height:64, borderRadius:'50%', background:'rgba(255,255,255,.12)', display:'flex', alignItems:'center', justifyContent:'center', border:'2px solid rgba(255,255,255,.2)' }}>
                <svg width={26} height={26} viewBox="0 0 24 24" fill="rgba(255,255,255,.7)"><polygon points="5,3 19,12 5,21"/></svg>
              </div>
              <div className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.12em', color:'rgba(255,255,255,.5)' }}>Add video URL in Admin → Hero</div>
            </div>
          )}

          {/* Corner badge — covers AI-video watermark in bottom-right */}
          {parsed && parsed.type === 'video' && (
            <div className="mono" style={{ position:'absolute', right:0, bottom:0, zIndex:3, background:'linear-gradient(135deg,#1E40AF,#2563EB)', color:'#fff', padding:'6px 12px', borderRadius:'12px 0 12px 0', fontSize:10, fontWeight:700, textTransform:'uppercase', letterSpacing:'0.12em', boxShadow:'0 4px 14px rgba(30,64,175,.45)', display:'flex', alignItems:'center', gap:6, pointerEvents:'none' }}>
              <span style={{ width:6, height:6, borderRadius:'50%', background:'#29B2FE', boxShadow:'0 0 8px #29B2FE' }} />
              Techpenta
            </div>
          )}
        </div>
      </div>
    </div>
  );
}

// ─── Hero Section ─────────────────────────────────────────────────────────────
function HeroSection({ data, onOpenQuote }) {
  const h = data.hero;
  const bullets = h.bullets || [];

  return (
    <section id="top" className="hero-banner" style={{ position:'relative', padding:'72px 5% 80px', background:'#EFF6FF', borderBottom:'1px solid #DBEAFE', overflow:'hidden' }}>
      {/* Background: techpenta gravity */}
      <div aria-hidden="true" style={{ position:'absolute', inset:0, pointerEvents:'none', zIndex:0 }}>
        <div style={{ position:'absolute', inset:0, display:'flex', alignItems:'center', justifyContent:'center' }}>
          <span style={{ fontSize:'22vw', fontWeight:900, letterSpacing:'-0.05em', color:'rgba(37,99,235,0.08)', whiteSpace:'nowrap', lineHeight:1, userSelect:'none' }}>
            techpenta
          </span>
        </div>
        <div style={{ position:'absolute', inset:0, pointerEvents:'auto' }}>
          <Gravity gravity={{ x: 0, y: 1 }} className="w-full h-full">
            <MatterBody matterBodyOptions={{ friction:0.5, restitution:0.3 }} x="15%" y="8%">
              <div className="tech-pill rounded-full px-6 py-2 text-white text-sm md:text-base font-medium shadow-lg hover:cursor-grab" style={{ background:'#2563EB' }}>react</div>
            </MatterBody>
            <MatterBody matterBodyOptions={{ friction:0.5, restitution:0.3 }} x="30%" y="18%" angle={-6}>
              <div className="tech-pill rounded-full px-6 py-2 text-white text-sm md:text-base font-medium shadow-lg hover:cursor-grab" style={{ background:'#3178c6' }}>typescript</div>
            </MatterBody>
            <MatterBody matterBodyOptions={{ friction:0.5, restitution:0.3 }} x="45%" y="6%">
              <div className="tech-pill rounded-full px-6 py-2 text-white text-sm md:text-base font-medium shadow-lg hover:cursor-grab" style={{ background:'#1f464d' }}>node.js</div>
            </MatterBody>
            <MatterBody matterBodyOptions={{ friction:0.5, restitution:0.3 }} x="62%" y="14%">
              <div className="tech-pill rounded-full px-6 py-2 text-white text-sm md:text-base font-medium shadow-lg hover:cursor-grab" style={{ background:'#06b6d4' }}>tailwind</div>
            </MatterBody>
            <MatterBody matterBodyOptions={{ friction:0.5, restitution:0.3 }} x="78%" y="8%" angle={8}>
              <div className="tech-pill rounded-full px-6 py-2 text-sm md:text-base font-medium shadow-lg hover:cursor-grab" style={{ background:'#ffd726', color:'#0F172A' }}>vite</div>
            </MatterBody>
            <MatterBody matterBodyOptions={{ friction:0.5, restitution:0.3 }} x="22%" y="32%">
              <div className="tech-pill rounded-full px-6 py-2 text-white text-sm md:text-base font-medium shadow-lg hover:cursor-grab" style={{ background:'#ff5941' }}>matter-js</div>
            </MatterBody>
            <MatterBody matterBodyOptions={{ friction:0.5, restitution:0.3 }} x="55%" y="30%">
              <div className="tech-pill rounded-full px-6 py-2 text-white text-sm md:text-base font-medium shadow-lg hover:cursor-grab" style={{ background:'#E794DA' }}>framer</div>
            </MatterBody>
            <MatterBody matterBodyOptions={{ friction:0.5, restitution:0.3 }} x="80%" y="32%" angle={-4}>
              <div className="tech-pill rounded-full px-6 py-2 text-white text-sm md:text-base font-medium shadow-lg hover:cursor-grab" style={{ background:'#08060d' }}>next.js</div>
            </MatterBody>
            <MatterBody matterBodyOptions={{ friction:0.5, restitution:0.3 }} x="10%" y="44%" angle={4}>
              <div className="tech-pill rounded-full px-6 py-2 text-white text-sm md:text-base font-medium shadow-lg hover:cursor-grab" style={{ background:'#21759B' }}>wordpress</div>
            </MatterBody>
            <MatterBody matterBodyOptions={{ friction:0.5, restitution:0.3 }} x="28%" y="46%" angle={-8}>
              <div className="tech-pill rounded-full px-6 py-2 text-white text-sm md:text-base font-medium shadow-lg hover:cursor-grab" style={{ background:'#FF2D20' }}>laravel</div>
            </MatterBody>
            <MatterBody matterBodyOptions={{ friction:0.5, restitution:0.3 }} x="44%" y="44%">
              <div className="tech-pill rounded-full px-6 py-2 text-white text-sm md:text-base font-medium shadow-lg hover:cursor-grab" style={{ background:'#777BB4' }}>php</div>
            </MatterBody>
            <MatterBody matterBodyOptions={{ friction:0.5, restitution:0.3 }} x="58%" y="46%" angle={6}>
              <div className="tech-pill rounded-full px-6 py-2 text-white text-sm md:text-base font-medium shadow-lg hover:cursor-grab" style={{ background:'#47A248' }}>mongodb</div>
            </MatterBody>
            <MatterBody matterBodyOptions={{ friction:0.5, restitution:0.3 }} x="72%" y="44%" angle={-3}>
              <div className="tech-pill rounded-full px-6 py-2 text-white text-sm md:text-base font-medium shadow-lg hover:cursor-grab" style={{ background:'#4479A1' }}>mysql</div>
            </MatterBody>
            <MatterBody matterBodyOptions={{ friction:0.5, restitution:0.3 }} x="85%" y="46%">
              <div className="tech-pill rounded-full px-6 py-2 text-white text-sm md:text-base font-medium shadow-lg hover:cursor-grab" style={{ background:'#7AB55C' }}>shopify</div>
            </MatterBody>
            <MatterBody matterBodyOptions={{ friction:0.5, restitution:0.3 }} x="40%" y="58%" angle={10}>
              <div className="tech-pill rounded-full px-6 py-2 text-sm md:text-base font-medium shadow-lg hover:cursor-grab" style={{ background:'#FF9900', color:'#0F172A' }}>aws</div>
            </MatterBody>
          </Gravity>
        </div>
      </div>

      <div className="resp-2col" style={{ position:'relative', zIndex:1, maxWidth:1200, margin:'0 auto' }}>

        {/* ── LEFT COLUMN ── */}
        <div>
          {/* Badge pill */}
          <div className="anim-fadeUp" style={{ marginBottom:22 }}>
            <span style={{ display:'inline-block', background:'rgba(59,130,246,.1)', border:'1px solid rgba(59,130,246,.25)', color:'#1E40AF', fontSize:13, fontWeight:500, padding:'6px 16px', borderRadius:99 }}>
              {h.badge}
            </span>
          </div>

          {/* Heading */}
          <h1 className="anim-fadeUp delay-100" style={{ fontSize:'clamp(2rem,3.6vw,3.2rem)', fontWeight:900, lineHeight:1.08, letterSpacing:'-0.02em', color:'#0F172A', marginBottom:10 }}>
            {h.headingMain || h.line1}
          </h1>
          <h1 className="anim-fadeUp delay-200" style={{ fontSize:'clamp(1.4rem,3vw,3.2rem)', fontWeight:900, lineHeight:1.08, letterSpacing:'-0.02em', color:'#2563EB', marginBottom:26, whiteSpace:'nowrap' }}>
            {h.headingAccent || h.line3}
          </h1>

          {/* Subheading */}
          {(h.subheading || h.description) && (
            <p className="anim-fadeUp delay-300" style={{ fontSize:16, color:'#334155', lineHeight:1.65, marginBottom:20 }}>
              {h.subheading || h.description}
            </p>
          )}

          {/* Bullets */}
          {bullets.length > 0 && (
            <ul className="anim-fadeUp delay-300" style={{ listStyle:'none', marginBottom:30 }}>
              {bullets.map((b,i) => (
                <li key={i} className="bullet-item" style={{ display:'flex', alignItems:'flex-start', gap:10, marginBottom:10, animationDelay:`${0.35 + i*0.08}s` }}>
                  <span style={{ width:7, height:7, borderRadius:'50%', background:'#2563EB', flexShrink:0, marginTop:7 }} />
                  <span style={{ fontSize:15, color:'#334155', lineHeight:1.5 }}>{b}</span>
                </li>
              ))}
            </ul>
          )}

          {/* CTA Button */}
          <div className="anim-fadeUp delay-400">
            <button type="button" onClick={() => onOpenQuote && onOpenQuote()}
              style={{ display:'inline-block', background:'#2563EB', color:'#fff', fontWeight:700, fontSize:14, letterSpacing:'0.06em', textTransform:'uppercase', padding:'16px 36px', borderRadius:8, border:'none', cursor:'pointer', transition:'background .2s, transform .15s, box-shadow .2s', boxShadow:'0 4px 16px rgba(37,99,235,.35)' }}
              onMouseEnter={e=>{e.currentTarget.style.background='#1D4ED8';e.currentTarget.style.transform='translateY(-2px)';e.currentTarget.style.boxShadow='0 8px 28px rgba(37,99,235,.45)';}}
              onMouseLeave={e=>{e.currentTarget.style.background='#2563EB';e.currentTarget.style.transform='none';e.currentTarget.style.boxShadow='0 4px 16px rgba(37,99,235,.35)';}}>
              {h.ctaText || 'Get a Free Quote'}
            </button>
          </div>
        </div>

        {/* ── RIGHT COLUMN — Video ── */}
        <div className="anim-fadeUp delay-300">
          <VideoPlayer url={h.videoUrl} quote={h.videoQuote} poster={h.videoPoster} />
        </div>

      </div>
    </section>
  );
}

// ─── Marquee ──────────────────────────────────────────────────────────────────
function MarqueeSection({ items }) {
  const doubled = [...(items||[]), ...(items||[])];
  return (
    <div style={{ borderTop:'1px solid #DBEAFE', borderBottom:'1px solid #DBEAFE', background:'#1E3A8A', overflow:'hidden', padding:'14px 0' }}>
      <div className="anim-marquee" style={{ display:'flex', whiteSpace:'nowrap', width:'max-content' }}>
        {doubled.map((item,i) => (
          <div key={i} style={{ display:'flex', alignItems:'center', gap:20, padding:'0 20px' }}>
            <span className="display" style={{ fontSize:22, color:'#fff' }}>{item}</span>
            <span style={{ color:'#60A5FA', fontSize:18 }}>✦</span>
          </div>
        ))}
      </div>
    </div>
  );
}

// ─── Portfolio Category Definitions for Sectioned Layout ─────────────────────
function getProjectSectionCategory(p) {
  if (!p) return 'Websites';
  if (p.type === 'app') return 'Apps';
  if (p.type === 'tool' || p.type === 'software') return 'Software';
  if (p.type === 'logo') return 'Brand & Logo';
  if (p.type === 'seo') return 'SEO & Marketing';
  return 'Websites';
}

const PORTFOLIO_CATEGORY_SECTIONS = [
  {
    id: 'Apps',
    anchor: 'section-apps',
    num: '01',
    label: 'Applications (Desktop & Mobile Apps)',
    shortLabel: 'Apps',
    icon: '📱',
    gradient: 'linear-gradient(135deg, #7C3AED 0%, #9333EA 100%)',
    accentColor: '#7C3AED',
    badgeBg: '#F5F3FF',
    badgeBorder: '#DDD6FE',
    tagline: 'Native macOS, Linux, Windows & Mobile (iOS / Android) Apps',
    desc: 'Bespoke native applications built for modern operating systems — Swift/SwiftUI for MacBook, Rust/GTK for Linux, C#/WinUI 3 for Windows, and fluid React Native for iOS & Android.',
    highlights: ['Multi-Platform Support (Mac, Linux, Windows, iOS, Android)', 'App Store & Notarized Installers', 'Offline Storage & Fast Sync', 'Fluid 60fps Native UX'],
    quoteCategory: 'Application Development'
  },
  {
    id: 'Websites',
    anchor: 'section-websites',
    num: '02',
    label: 'High-Performance Websites & eCommerce Stores',
    shortLabel: 'Websites',
    icon: '🌐',
    gradient: 'linear-gradient(135deg, #1E40AF 0%, #3B82F6 100%)',
    accentColor: '#1E40AF',
    badgeBg: '#EFF6FF',
    badgeBorder: '#BFDBFE',
    tagline: 'Authority Corporate Websites & High-Converting eCommerce Brands',
    desc: 'Modern, mobile-first websites and DTC online stores engineered to establish instant authority, rank high on Google, and convert visitors into paying clients.',
    highlights: ['Sub-1.2s Load Speeds', 'Shopify & WooCommerce Masters', 'Mobile Purchasing Conversion', '99+ Lighthouse Scores'],
    quoteCategory: 'Business Website'
  },
  {
    id: 'Software',
    anchor: 'section-software',
    num: '03',
    label: 'Custom Software, Cloud Platforms & SaaS Systems',
    shortLabel: 'Software',
    icon: '⚙️',
    gradient: 'linear-gradient(135deg, #D97706 0%, #F59E0B 100%)',
    accentColor: '#D97706',
    badgeBg: '#FEF3C7',
    badgeBorder: '#FDE68A',
    tagline: 'Bespoke Internal Systems, Interactive Cloud Portals & SaaS Tools',
    desc: 'Custom software systems and reactive dashboards that automate manual business processes, eliminate repetitive administrative tasks, and replace expensive recurring SaaS subscriptions.',
    highlights: ['Operational Cost Reduction', 'React & Next.js Cloud Architecture', 'Automated Business Workflows', 'Zero Recurring License Fees'],
    quoteCategory: 'Custom Software / Tool'
  },
  {
    id: 'Brand & Logo',
    anchor: 'section-branding',
    num: '04',
    label: 'Brand Identity & Vector Logo Design',
    shortLabel: 'Brand & Logo',
    icon: '🎨',
    gradient: 'linear-gradient(135deg, #E11D48 0%, #F43F5E 100%)',
    accentColor: '#E11D48',
    badgeBg: '#FFF1F2',
    badgeBorder: '#FECDD3',
    tagline: 'Memorable Brand Visuals, Vector Marks & Identity Systems',
    desc: 'Distinctive visual identities that command authority in competitive markets. Complete with scalable vector logos, color psychology palettes, typography guides, and brand books.',
    highlights: ['Scalable Vector Source Files', 'Comprehensive Style Guides', 'Print & Digital Optimization', 'Trademark-Ready Originals'],
    quoteCategory: 'Brand & Logo Design'
  },
  {
    id: 'SEO & Marketing',
    anchor: 'section-seo',
    num: '05',
    label: 'SEO & Search Dominance Campaigns',
    shortLabel: 'SEO & Growth',
    icon: '📈',
    gradient: 'linear-gradient(135deg, #0891B2 0%, #06B6D4 100%)',
    accentColor: '#0891B2',
    badgeBg: '#ECFEFF',
    badgeBorder: '#A5F3FC',
    tagline: 'Google Ranking Dominance & Predictable Organic Inbound Leads',
    desc: 'Data-driven search engine optimization and digital growth campaigns that place your brand at the very top of Google when high-intent prospects search.',
    highlights: ['Top 3 Local Map Pack Rankings', 'High-Intent Buyer Keywords', 'Technical Schema Architecture', 'Consistent Inbound Inquiries'],
    quoteCategory: 'SEO & Digital Marketing'
  }
];

function CategoryJumpDock({ sections, activeSection, onJumpToSection }) {
  return (
    <div className="cat-jump-dock" role="navigation" aria-label="Category Quick Navigation">
      <div className="mono" style={{ fontSize:10.5, textTransform:'uppercase', color:'#1E40AF', fontWeight:700, padding:'0 8px', letterSpacing:'0.08em', whiteSpace:'nowrap', display:'flex', alignItems:'center', gap:5 }}>
        <Sparkles size={13} style={{ color:'#2563EB' }} /> Jump To:
      </div>
      {sections.map(sec => {
        const isActive = activeSection === sec.anchor;
        return (
          <button
            key={sec.anchor}
            onClick={() => onJumpToSection(sec.anchor)}
            className={`mono cat-dock-pill ${isActive ? 'active' : ''}`}
            style={{
              background: isActive ? sec.accentColor : '#FFFFFF',
              color: isActive ? '#FFFFFF' : '#1E293B',
              borderColor: isActive ? sec.accentColor : '#DBEAFE',
              boxShadow: isActive ? `0 4px 14px ${sec.accentColor}35` : 'none'
            }}
          >
            <span>{sec.icon}</span>
            <span>{sec.shortLabel}</span>
            <span style={{
              fontSize:9.5,
              padding:'1px 6px',
              borderRadius:99,
              background: isActive ? 'rgba(255,255,255,.28)' : '#EFF6FF',
              color: isActive ? '#FFFFFF' : '#2563EB',
              fontWeight: 700
            }}>
              {sec.items.length}
            </span>
          </button>
        );
      })}
    </div>
  );
}

function CategorySectionBlock({ sec, index, totalSections, onSelect, onOpenQuote, setCategoryFilter }) {
  const [ref, vis] = useReveal();

  return (
    <div id={sec.anchor} style={{ scrollMarginTop: 130, marginBottom: index === totalSections - 1 ? 0 : 44 }}>
      {/* Category Section Header Banner */}
      <div
        ref={ref}
        className={`reveal ${vis ? 'in' : ''} cat-section-header`}
        style={{
          borderLeft: `5px solid ${sec.accentColor}`,
          position: 'relative',
          background: '#FFFFFF',
          borderRadius: 22,
          padding: '28px 30px',
          marginBottom: 28,
          boxShadow: '0 8px 32px rgba(30,64,175,.05)'
        }}
      >
        <div style={{ display:'flex', flexWrap:'wrap', justifyContent:'space-between', alignItems:'flex-start', gap:20 }}>
          <div style={{ maxWidth:780 }}>
            {/* Eyebrow / Tag */}
            <div style={{ display:'flex', alignItems:'center', gap:10, marginBottom:10, flexWrap:'wrap' }}>
              <span style={{
                display:'inline-flex',
                alignItems:'center',
                gap:6,
                padding:'4px 12px',
                borderRadius:99,
                background: sec.badgeBg,
                color: sec.accentColor,
                border: `1px solid ${sec.badgeBorder}`,
                fontSize: 11,
                fontFamily:'Geist Mono, monospace',
                fontWeight: 700,
                letterSpacing:'0.06em',
                textTransform:'uppercase'
              }}>
                <span>{sec.icon}</span>
                <span>CATEGORY {sec.num} · {sec.shortLabel}</span>
              </span>

              <span style={{
                display:'inline-flex',
                alignItems:'center',
                gap:5,
                padding:'4px 10px',
                borderRadius:99,
                background: '#F1F5F9',
                color: '#475569',
                fontSize: 11,
                fontFamily:'Geist Mono, monospace',
                fontWeight: 600
              }}>
                <CheckCircle2 size={12} style={{ color: sec.accentColor }} />
                {sec.items.length} {sec.items.length === 1 ? 'Project' : 'Projects'}
              </span>
            </div>

            {/* Title */}
            <h3 className="display" style={{ fontSize:'clamp(1.7rem, 3vw, 2.3rem)', color:'#0F172A', lineHeight:1.2, margin:'0 0 8px' }}>
              {sec.label}
            </h3>

            {/* Tagline */}
            <div style={{ fontSize:14.5, fontWeight:600, color: sec.accentColor, marginBottom:8 }}>
              {sec.tagline}
            </div>

            {/* Non-technical Description */}
            <p style={{ fontSize:14, color:'#475569', lineHeight:1.55, margin:'0 0 16px', maxWidth:700 }}>
              {sec.desc}
            </p>

            {/* Capability Highlights */}
            <div style={{ display:'flex', flexWrap:'wrap', gap:8 }}>
              {sec.highlights.map((h, i) => (
                <span
                  key={i}
                  style={{
                    fontSize: 11.5,
                    color: '#334155',
                    background: '#F8FAFC',
                    border: '1px solid #E2E8F0',
                    borderRadius: 99,
                    padding: '3px 10px',
                    display: 'inline-flex',
                    alignItems: 'center',
                    gap: 5
                  }}
                >
                  <span style={{ color: sec.accentColor, fontWeight: 700 }}>✓</span> {h}
                </span>
              ))}
            </div>
          </div>

          {/* Quick Category Action CTAs */}
          <div style={{ display:'flex', flexDirection:'column', gap:10, flexShrink:0, alignSelf:'flex-start' }}>
            <button
              onClick={() => onOpenQuote({ title: sec.label, type: sec.quoteCategory })}
              className="mono"
              style={{
                display:'inline-flex',
                alignItems:'center',
                gap:8,
                padding:'11px 20px',
                borderRadius:99,
                background: sec.gradient,
                color:'#FFFFFF',
                fontSize:11.5,
                fontWeight:700,
                border:'none',
                cursor:'pointer',
                boxShadow:'0 6px 20px rgba(0,0,0,.12)',
                transition:'all .2s ease'
              }}
              onMouseEnter={e => e.currentTarget.style.transform = 'translateY(-2px)'}
              onMouseLeave={e => e.currentTarget.style.transform = 'translateY(0)'}
            >
              Discuss {sec.shortLabel} Project <ArrowUpRight size={14} />
            </button>

            <button
              onClick={() => setCategoryFilter(sec.id)}
              className="mono"
              style={{
                display:'inline-flex',
                alignItems:'center',
                justifyContent:'center',
                gap:6,
                padding:'8px 16px',
                borderRadius:99,
                background:'#FFFFFF',
                color: sec.accentColor,
                border:`1px solid ${sec.badgeBorder}`,
                fontSize:11,
                fontWeight:600,
                cursor:'pointer',
                transition:'all .15s ease'
              }}
              onMouseEnter={e => { e.currentTarget.style.background = sec.badgeBg; }}
              onMouseLeave={e => { e.currentTarget.style.background = '#FFFFFF'; }}
            >
              Focus on this Category ({sec.items.length}) →
            </button>
          </div>
        </div>
      </div>

      {/* Projects Grid for this Category */}
      <div style={{ display:'grid', gridTemplateColumns:'repeat(auto-fill, minmax(350px, 1fr))', gap:'36px 28px' }}>
        {sec.items.map((p, i) => (
          <ProjectCard key={p.id} p={p} i={i} onSelect={onSelect} onOpenQuote={onOpenQuote} />
        ))}
      </div>

      {/* In-Between Category Divider with Milestone Node */}
      {index < totalSections - 1 && (
        <div className="cat-divider">
          <div className="cat-divider-node">
            <span>✦</span>
            <span>NEXT: {PORTFOLIO_CATEGORY_SECTIONS[index + 1]?.shortLabel || 'CATEGORY'}</span>
            <span>✦</span>
          </div>
        </div>
      )}
    </div>
  );
}

// ─── Work ─────────────────────────────────────────────────────────────────────
function WorkSection({
  projects,
  filtered,
  categories,
  categoryFilter,
  setCategoryFilter,
  techFilter,
  setTechFilter,
  techOptions,
  industryFilter,
  setIndustryFilter,
  industries,
  searchQuery,
  setSearchQuery,
  onSelect,
  onOpenQuote
}) {
  const [ref, vis] = useReveal();
  const [activeSection, setActiveSection] = useState('section-apps');

  const isDefaultView = categoryFilter === 'all' && techFilter === 'all' && industryFilter === 'all' && !searchQuery.trim();
  const activeCategory = categories.find(c => c.id === categoryFilter) || categories[0];
  const hasActiveFilters = categoryFilter !== 'all' || techFilter !== 'all' || industryFilter !== 'all' || searchQuery.trim() !== '';

  // Categorized project groups for the All Projects sectioned layout
  const categorySectionsWithProjects = useMemo(() => {
    return PORTFOLIO_CATEGORY_SECTIONS.map(sec => {
      const items = filtered.filter(p => getProjectSectionCategory(p) === sec.id);
      return {
        ...sec,
        items
      };
    }).filter(sec => sec.items.length > 0);
  }, [filtered]);

  // Real-time scroll spy for active category jump dock pill
  useEffect(() => {
    if (categoryFilter !== 'all') return;
    const handleScroll = () => {
      for (let i = categorySectionsWithProjects.length - 1; i >= 0; i--) {
        const sec = categorySectionsWithProjects[i];
        const el = document.getElementById(sec.anchor);
        if (el) {
          const rect = el.getBoundingClientRect();
          if (rect.top <= 260) {
            setActiveSection(sec.anchor);
            break;
          }
        }
      }
    };
    window.addEventListener('scroll', handleScroll, { passive: true });
    return () => window.removeEventListener('scroll', handleScroll);
  }, [categoryFilter, categorySectionsWithProjects]);

  const handleJumpToSection = (anchor) => {
    const el = document.getElementById(anchor);
    if (el) {
      const headerOffset = 130;
      const elementPosition = el.getBoundingClientRect().top;
      const offsetPosition = elementPosition + window.pageYOffset - headerOffset;
      window.scrollTo({
        top: offsetPosition,
        behavior: 'smooth'
      });
      setActiveSection(anchor);
    }
  };

  const resetFilters = () => {
    setCategoryFilter('all');
    setTechFilter('all');
    setIndustryFilter('all');
    setSearchQuery('');
  };

  return (
    <section id="work" style={{ padding:'80px 5% 40px', background:'#F0F7FF', position:'relative' }}>
      <div style={{ maxWidth:1240, margin:'0 auto' }}>
        
        {/* Section Header */}
        <div ref={ref} className={`reveal ${vis?'in':''}`} style={{ marginBottom:36 }}>
          <div style={{ display:'flex', flexWrap:'wrap', justifyContent:'space-between', alignItems:'flex-end', gap:20, marginBottom:16 }}>
            <div style={{ maxWidth:740 }}>
              <div className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.15em', color:'#2563EB', marginBottom:10, display:'flex', alignItems:'center', gap:8, fontWeight:700 }}>
                <span style={{ display:'inline-block', width:8, height:8, borderRadius:'50%', background:'#2563EB' }} />
                § Client Portfolio & Case Studies
              </div>
              <h2 className="display" style={{ fontSize:'clamp(2.4rem,5.2vw,4.2rem)', color:'#0F172A', lineHeight:1.1, marginBottom:14 }}>
                Solutions built to <span className="display-it" style={{ color:'#1E40AF' }}>grow your business</span>.
              </h2>
              <p style={{ fontSize:16, color:'#475569', lineHeight:1.6, maxWidth:640 }}>
                We don’t just write code. We design and engineer websites, mobile apps, and custom software that solve real operational bottlenecks, attract paying customers, and deliver measurable ROI.
              </p>
            </div>

            {/* Quick Action CTA */}
            <div style={{ textAlign:'right' }}>
              <button
                onClick={() => onOpenQuote()}
                className="btn-primary mono"
                style={{ display:'inline-flex', alignItems:'center', gap:8, padding:'14px 26px', borderRadius:99, fontSize:12, textTransform:'uppercase', letterSpacing:'0.1em', cursor:'pointer', boxShadow:'0 10px 25px rgba(30,64,175,.25)' }}
              >
                Discuss Your Project <ArrowUpRight size={15} />
              </button>
              <div className="mono" style={{ fontSize:10.5, color:'#64748B', marginTop:8 }}>
                Free initial scope & cost estimate · 24h response
              </div>
            </div>
          </div>

          {/* Trust strip */}
          <div style={{ display:'grid', gridTemplateColumns:'repeat(auto-fit, minmax(200px, 1fr))', gap:12, padding:'16px 20px', background:'#FFFFFF', border:'1px solid #DBEAFE', borderRadius:16, marginTop:24, boxShadow:'0 4px 16px rgba(30,64,175,.04)' }}>
            <div style={{ display:'flex', alignItems:'center', gap:10 }}>
              <div style={{ width:36, height:36, borderRadius:10, background:'#EFF6FF', color:'#1E40AF', display:'flex', alignItems:'center', justifyContent:'center', flexShrink:0 }}>
                <Award size={18} />
              </div>
              <div>
                <div style={{ fontWeight:700, fontSize:15, color:'#0F172A' }}>2,500+ Projects</div>
                <div className="mono" style={{ fontSize:10, color:'#64748B' }}>Delivered Worldwide</div>
              </div>
            </div>
            <div style={{ display:'flex', alignItems:'center', gap:10 }}>
              <div style={{ width:36, height:36, borderRadius:10, background:'#ECFDF5', color:'#059669', display:'flex', alignItems:'center', justifyContent:'center', flexShrink:0 }}>
                <Clock size={18} />
              </div>
              <div>
                <div style={{ fontWeight:700, fontSize:15, color:'#0F172A' }}>18+ Years Track Record</div>
                <div className="mono" style={{ fontSize:10, color:'#64748B' }}>Established in 2010</div>
              </div>
            </div>
            <div style={{ display:'flex', alignItems:'center', gap:10 }}>
              <div style={{ width:36, height:36, borderRadius:10, background:'#FEF3C7', color:'#D97706', display:'flex', alignItems:'center', justifyContent:'center', flexShrink:0 }}>
                <Users size={18} />
              </div>
              <div>
                <div style={{ fontWeight:700, fontSize:15, color:'#0F172A' }}>98% Retention Rate</div>
                <div className="mono" style={{ fontSize:10, color:'#64748B' }}>Long-Term Client Trust</div>
              </div>
            </div>
            <div style={{ display:'flex', alignItems:'center', gap:10 }}>
              <div style={{ width:36, height:36, borderRadius:10, background:'#F5F3FF', color:'#7C3AED', display:'flex', alignItems:'center', justifyContent:'center', flexShrink:0 }}>
                <Shield size={18} />
              </div>
              <div>
                <div style={{ fontWeight:700, fontSize:15, color:'#0F172A' }}>180 Days Free Support</div>
                <div className="mono" style={{ fontSize:10, color:'#64748B' }}>Post-Launch Warranty</div>
              </div>
            </div>
          </div>
        </div>

        {/* Categories Navigation Bar */}
        <div style={{ marginBottom:18 }}>
          <div className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.1em', color:'#64748B', marginBottom:10, fontWeight:600 }}>
            Select Project Category:
          </div>
          <div style={{ display:'flex', flexWrap:'wrap', gap:10, alignItems:'center' }}>
            {categories.map(c => {
              const active = categoryFilter === c.id;
              return (
                <button
                  key={c.id}
                  onClick={() => setCategoryFilter(c.id)}
                  className="mono"
                  style={{
                    display:'inline-flex',
                    alignItems:'center',
                    gap:8,
                    padding:'10px 18px',
                    borderRadius:99,
                    border: active ? '1.5px solid #1E40AF' : '1.5px solid #BFDBFE',
                    background: active ? '#1E40AF' : '#FFFFFF',
                    color: active ? '#FFFFFF' : '#1E40AF',
                    fontSize:11.5,
                    fontWeight: active ? 600 : 500,
                    cursor:'pointer',
                    whiteSpace:'nowrap',
                    transition:'all .2s ease',
                    boxShadow: active ? '0 6px 18px rgba(30,64,175,.2)' : '0 2px 6px rgba(30,64,175,.04)'
                  }}
                  onMouseEnter={e => {
                    if (!active) { e.currentTarget.style.borderColor = '#3B82F6'; e.currentTarget.style.background = '#EFF6FF'; }
                  }}
                  onMouseLeave={e => {
                    if (!active) { e.currentTarget.style.borderColor = '#BFDBFE'; e.currentTarget.style.background = '#FFFFFF'; }
                  }}
                >
                  <span>{c.icon}</span>
                  <span>{c.label}</span>
                  <span style={{
                    fontSize:10,
                    padding:'2px 7px',
                    borderRadius:99,
                    background: active ? 'rgba(255,255,255,.25)' : '#EFF6FF',
                    color: active ? '#fff' : '#2563EB',
                    fontWeight:700
                  }}>
                    {c.count}
                  </span>
                </button>
              );
            })}
          </div>
        </div>

        {/* Tech Stack / Platform Filter Bar */}
        <div style={{
          marginBottom: 20,
          padding: '16px 20px',
          background: '#FFFFFF',
          border: '1.5px solid #DBEAFE',
          borderRadius: 18,
          boxShadow: '0 4px 16px rgba(30,64,175,.04)'
        }}>
          <div style={{ display: 'flex', alignItems: 'center', justifyContent: 'space-between', marginBottom: 12, flexWrap: 'wrap', gap: 10 }}>
            <div className="mono" style={{ fontSize: 11, textTransform: 'uppercase', letterSpacing: '0.12em', color: '#1E40AF', fontWeight: 700, display: 'flex', alignItems: 'center', gap: 7 }}>
              <span style={{ display:'inline-block', width:7, height:7, borderRadius:'50%', background:'#2563EB' }} />
              <span>⚡ Tech Stack / Platform Filter:</span>
            </div>
            {techFilter !== 'all' && (
              <button
                onClick={() => setTechFilter('all')}
                className="mono"
                style={{
                  fontSize: 10.5,
                  color: '#DC2626',
                  background: '#FEF2F2',
                  border: '1px solid #FECACA',
                  borderRadius: 99,
                  padding: '3px 10px',
                  cursor: 'pointer',
                  fontWeight: 600,
                  display: 'inline-flex',
                  alignItems: 'center',
                  gap: 4,
                  transition: 'background .15s'
                }}
                onMouseEnter={e => e.currentTarget.style.background = '#FEE2E2'}
                onMouseLeave={e => e.currentTarget.style.background = '#FEF2F2'}
              >
                ✕ Clear Tech ({techFilter})
              </button>
            )}
          </div>

          {/* Tech Chips */}
          <div style={{ display: 'flex', flexWrap: 'wrap', gap: 8, alignItems: 'center' }}>
            {techOptions.map(t => {
              const active = techFilter === t.id;
              return (
                <button
                  key={t.id}
                  onClick={() => setTechFilter(active ? 'all' : t.id)}
                  className="mono"
                  style={{
                    display: 'inline-flex',
                    alignItems: 'center',
                    gap: 6,
                    padding: '7px 13px',
                    borderRadius: 99,
                    border: active ? '1.5px solid #1E40AF' : '1px solid #DBEAFE',
                    background: active ? '#1E40AF' : '#F8FAFC',
                    color: active ? '#FFFFFF' : '#334155',
                    fontSize: 11,
                    fontWeight: active ? 700 : 500,
                    cursor: 'pointer',
                    whiteSpace: 'nowrap',
                    transition: 'all .15s ease',
                    boxShadow: active ? '0 4px 14px rgba(30,64,175,.25)' : 'none'
                  }}
                  onMouseEnter={e => {
                    if (!active) { e.currentTarget.style.borderColor = '#93C5FD'; e.currentTarget.style.background = '#EFF6FF'; e.currentTarget.style.color = '#1E40AF'; }
                  }}
                  onMouseLeave={e => {
                    if (!active) { e.currentTarget.style.borderColor = '#DBEAFE'; e.currentTarget.style.background = '#F8FAFC'; e.currentTarget.style.color = '#334155'; }
                  }}
                >
                  <span>{t.icon}</span>
                  <span>{t.label}</span>
                  <span style={{
                    fontSize: 9.5,
                    padding: '1px 6px',
                    borderRadius: 99,
                    background: active ? 'rgba(255,255,255,.28)' : '#EFF6FF',
                    color: active ? '#FFFFFF' : '#2563EB',
                    fontWeight: 700
                  }}>
                    {t.count}
                  </span>
                </button>
              );
            })}
          </div>

          {/* Active Tech State Feedback Strip */}
          {techFilter !== 'all' && (
            <div style={{
              marginTop: 12,
              paddingTop: 10,
              borderTop: '1px solid #EEF2F6',
              display: 'flex',
              alignItems: 'center',
              justifyContent: 'space-between',
              fontSize: 11.5,
              color: '#475569',
              flexWrap: 'wrap',
              gap: 8
            }}>
              <span className="mono">
                Showing <strong>{filtered.length}</strong> projects built with <strong>{techFilter}</strong>
              </span>
              <button
                onClick={() => setTechFilter('all')}
                style={{ background: 'none', border: 'none', color: '#2563EB', cursor: 'pointer', fontWeight: 600, fontSize: 11.5 }}
              >
                View All Stacks →
              </button>
            </div>
          )}
        </div>

        {/* Secondary Filter & Search Row */}
        <div style={{ display:'flex', flexWrap:'wrap', alignItems:'center', justifyContent:'space-between', gap:14, padding:'16px 20px', background:'#FFFFFF', border:'1px solid #DBEAFE', borderRadius:16, marginBottom:28, boxShadow:'0 2px 10px rgba(30,64,175,.04)' }}>
          {/* Search Box */}
          <div style={{ position:'relative', flex:1, minWidth:260, maxWidth:420 }}>
            <Search size={15} style={{ position:'absolute', left:14, top:'50%', transform:'translateY(-50%)', color:'#94A3B8', pointerEvents:'none' }} />
            <input
              type="text"
              placeholder="Search projects, client names, features..."
              value={searchQuery}
              onChange={e => setSearchQuery(e.target.value)}
              style={{
                width:'100%',
                padding:'9px 36px 9px 38px',
                borderRadius:99,
                border:'1px solid #CBD5E1',
                background:'#F8FAFC',
                fontSize:12.5,
                color:'#0F172A',
                outline:'none',
                transition:'border-color .15s'
              }}
              onFocus={e => e.target.style.borderColor = '#2563EB'}
              onBlur={e => e.target.style.borderColor = '#CBD5E1'}
            />
            {searchQuery && (
              <button
                onClick={() => setSearchQuery('')}
                style={{ position:'absolute', right:12, top:'50%', transform:'translateY(-50%)', background:'none', border:'none', color:'#94A3B8', cursor:'pointer', fontSize:14 }}
              >
                ✕
              </button>
            )}
          </div>

          {/* Industry Filter Dropdown */}
          <div style={{ display:'flex', alignItems:'center', gap:8 }}>
            <span className="mono" style={{ fontSize:11, color:'#64748B', textTransform:'uppercase', letterSpacing:'0.06em' }}>Industry:</span>
            <select
              value={industryFilter}
              onChange={e => setIndustryFilter(e.target.value)}
              className="mono"
              style={{
                padding:'8px 14px',
                borderRadius:99,
                border:'1px solid #BFDBFE',
                background:'#F8FAFC',
                fontSize:11.5,
                color:'#1E40AF',
                fontWeight:500,
                cursor:'pointer',
                outline:'none'
              }}
            >
              <option value="all">All Industries ({projects.length})</option>
              {industries.filter(i => i !== 'all').map(ind => (
                <option key={ind} value={ind}>{ind}</option>
              ))}
            </select>
          </div>

          {/* Active Count & Clear Button */}
          <div style={{ display:'flex', alignItems:'center', gap:10 }}>
            <span className="mono" style={{ fontSize:11, color:'#64748B', textTransform:'uppercase', letterSpacing:'0.08em' }}>
              Showing <strong>{filtered.length}</strong> of {projects.length}
            </span>
            {hasActiveFilters && (
              <button
                onClick={resetFilters}
                className="mono"
                style={{
                  fontSize:10.5,
                  textTransform:'uppercase',
                  letterSpacing:'0.08em',
                  color:'#EF4444',
                  background:'#FEF2F2',
                  border:'1px solid #FECACA',
                  borderRadius:99,
                  padding:'4px 10px',
                  cursor:'pointer',
                  transition:'background .15s'
                }}
              >
                ✕ Reset Filters
              </button>
            )}
          </div>
        </div>

        {/* Flagship Success Showcase (Spotlight on All Projects) */}
        {isDefaultView && (
          <SpotlightSection onSelect={onSelect} onOpenQuote={onOpenQuote} projects={projects} />
        )}

        {/* Category Description Banner */}
        {categoryFilter !== 'all' && (
          <div style={{ padding:'14px 20px', background:'#EFF6FF', borderLeft:'4px solid #1E40AF', borderRadius:'0 12px 12px 0', marginBottom:28 }}>
            <h3 style={{ fontSize:16, fontWeight:700, color:'#0F172A', margin:'0 0 4px' }}>
              {activeCategory.label} Portfolio
            </h3>
            <p style={{ fontSize:13, color:'#475569', margin:0 }}>
              {activeCategory.desc}. Every project is engineered for speed, mobile responsiveness, and client ROI.
            </p>
          </div>
        )}

        {/* Projects Display: Separated Category Sections when viewing All Projects, or Focused View when filtering */}
        {filtered.length === 0 ? (
          <div style={{ padding:'60px 20px', textAlign:'center', background:'#fff', borderRadius:20, border:'1px solid #DBEAFE', margin:'20px 0' }}>
            <div style={{ fontSize:40, marginBottom:12 }}>🔍</div>
            <h3 className="display" style={{ fontSize:24, color:'#0F172A', marginBottom:8 }}>No matching projects found</h3>
            <p style={{ fontSize:14, color:'#64748B', maxWidth:440, margin:'0 auto 20px' }}>
              We didn't find any projects matching your search criteria. However, we likely have built custom solutions in your sector that are not public yet.
            </p>
            <div style={{ display:'flex', gap:10, justifyContent:'center', flexWrap:'wrap' }}>
              <button onClick={resetFilters} className="btn-secondary mono" style={{ padding:'10px 22px', borderRadius:99, fontSize:11, cursor:'pointer' }}>
                Clear Filters
              </button>
              <button onClick={() => onOpenQuote()} className="btn-primary mono" style={{ padding:'10px 22px', borderRadius:99, fontSize:11, cursor:'pointer' }}>
                Ask Us About Your Project →
              </button>
            </div>
          </div>
        ) : categoryFilter === 'all' ? (
          /* Category-Separated Layout for All Projects */
          <div>
            {/* Sticky Category Quick Jump Dock */}
            <CategoryJumpDock
              sections={categorySectionsWithProjects}
              activeSection={activeSection}
              onJumpToSection={handleJumpToSection}
            />

            {categorySectionsWithProjects.map((sec, secIdx) => {
              const showMidLead = secIdx === 1; // High-converting lead card after Websites section
              return (
                <React.Fragment key={sec.id}>
                  <CategorySectionBlock
                    sec={sec}
                    index={secIdx}
                    totalSections={categorySectionsWithProjects.length}
                    onSelect={onSelect}
                    onOpenQuote={onOpenQuote}
                    setCategoryFilter={setCategoryFilter}
                  />
                  {showMidLead && (
                    <div style={{ margin: '48px 0' }}>
                      <InGridLeadCard onOpenQuote={onOpenQuote} />
                    </div>
                  )}
                </React.Fragment>
              );
            })}
          </div>
        ) : (
          /* Single Focused Category Grid */
          <div>
            <div style={{ display:'flex', justifyContent:'space-between', alignItems:'center', marginBottom:24, flexWrap:'wrap', gap:10, padding:'12px 18px', background:'#FFFFFF', border:'1px solid #DBEAFE', borderRadius:14 }}>
              <div className="mono" style={{ fontSize:12, color:'#475569' }}>
                Viewing <strong>{filtered.length}</strong> verified projects in <strong>{activeCategory.label}</strong>
              </div>
              <button
                onClick={() => setCategoryFilter('all')}
                className="mono"
                style={{
                  display:'inline-flex',
                  alignItems:'center',
                  gap:6,
                  padding:'6px 14px',
                  borderRadius:99,
                  border:'1px solid #BFDBFE',
                  background:'#EFF6FF',
                  color:'#1E40AF',
                  fontSize:11.5,
                  cursor:'pointer',
                  fontWeight:600,
                  transition:'all .15s'
                }}
                onMouseEnter={e => { e.currentTarget.style.background = '#DBEAFE'; }}
                onMouseLeave={e => { e.currentTarget.style.background = '#EFF6FF'; }}
              >
                ← View All Categories Separated by Section
              </button>
            </div>

            <div style={{ display:'grid', gridTemplateColumns:'repeat(auto-fill, minmax(350px, 1fr))', gap:'36px 28px' }}>
              {filtered.map((p, i) => {
                const showLeadCard = (i > 0 && i % 6 === 0);
                return (
                  <React.Fragment key={p.id}>
                    {showLeadCard && (
                      <InGridLeadCard onOpenQuote={onOpenQuote} />
                    )}
                    <ProjectCard p={p} i={i} onSelect={onSelect} onOpenQuote={onOpenQuote} />
                  </React.Fragment>
                );
              })}
            </div>
          </div>
        )}

        {/* Trust & Process Section */}
        <TrustProcessSection onOpenQuote={onOpenQuote} />

      </div>
    </section>
  );
}

// ─── Flagship Spotlight ───────────────────────────────────────────────────────
function SpotlightSection({ projects, onSelect, onOpenQuote }) {
  const [ref, vis] = useReveal();
  // Select 4 marquee projects across diverse categories
  const spotlightIds = [1, 8, 35, 56]; // ALPHA E-BIKE, 702 Print, AstroWebGuru App, Drivault Mac App
  const spotlightItems = spotlightIds.map(id => projects.find(p => p.id === id)).filter(Boolean);

  if (spotlightItems.length === 0) return null;

  return (
    <div ref={ref} className={`reveal ${vis ? 'in' : ''}`} style={{ marginBottom:44, padding:'28px', background:'#FFFFFF', border:'1.5px solid #BFDBFE', borderRadius:24, boxShadow:'0 12px 36px rgba(30,64,175,.08)' }}>
      <div style={{ display:'flex', flexWrap:'wrap', justifyContent:'space-between', alignItems:'flex-end', gap:12, marginBottom:22, paddingBottom:16, borderBottom:'1px solid #E2E8F0' }}>
        <div>
          <div className="mono" style={{ fontSize:10.5, textTransform:'uppercase', letterSpacing:'0.12em', color:'#2563EB', fontWeight:700, marginBottom:4 }}>
            ✦ Featured Client Case Studies
          </div>
          <h3 className="display" style={{ fontSize:24, color:'#0F172A', margin:0 }}>
            Proven business impact across <span className="display-it" style={{ color:'#1E40AF' }}>every digital format</span>.
          </h3>
        </div>
        <p className="mono" style={{ fontSize:11, color:'#64748B', maxWidth:320, margin:0 }}>
          From high-volume eCommerce to custom full-stack software and native apps.
        </p>
      </div>

      <div style={{ display:'grid', gridTemplateColumns:'repeat(auto-fit, minmax(250px, 1fr))', gap:20 }}>
        {spotlightItems.map(p => (
          <div
            key={p.id}
            onClick={() => onSelect(p)}
            style={{
              background:'#F8FAFC',
              border:'1px solid #DBEAFE',
              borderRadius:16,
              padding:18,
              cursor:'pointer',
              transition:'all .25s ease',
              display:'flex',
              flexDirection:'column'
            }}
            onMouseEnter={e => {
              e.currentTarget.style.background = '#FFFFFF';
              e.currentTarget.style.borderColor = '#3B82F6';
              e.currentTarget.style.transform = 'translateY(-4px)';
              e.currentTarget.style.boxShadow = '0 10px 24px rgba(30,64,175,.12)';
            }}
            onMouseLeave={e => {
              e.currentTarget.style.background = '#F8FAFC';
              e.currentTarget.style.borderColor = '#DBEAFE';
              e.currentTarget.style.transform = 'translateY(0)';
              e.currentTarget.style.boxShadow = 'none';
            }}
          >
            <div style={{ display:'flex', justifyContent:'space-between', alignItems:'center', marginBottom:10 }}>
              <span className="mono" style={{ fontSize:9.5, padding:'3px 8px', background:'#EFF6FF', color:'#1E40AF', borderRadius:99, fontWeight:600 }}>
                {p.displayType || p.siteType}
              </span>
              <span className="mono" style={{ fontSize:10, color:'#059669', fontWeight:700 }}>
                {p.impact}
              </span>
            </div>
            
            <h4 style={{ fontSize:16, fontWeight:700, color:'#0F172A', margin:'0 0 6px' }}>{p.displayTitle || p.title}</h4>
            <p style={{ fontSize:12.5, color:'#475569', lineHeight:1.5, marginBottom:14, flex:1 }}>
              {p.businessSummary || p.tagline}
            </p>

            <div style={{ display:'flex', alignItems:'center', justifyContent:'space-between', paddingTop:10, borderTop:'1px solid #E2E8F0', marginTop:'auto' }}>
              <span className="mono" style={{ fontSize:10, color:'#64748B' }}>{p.industry}</span>
              <span className="mono" style={{ fontSize:11, color:'#1E40AF', fontWeight:600, display:'flex', alignItems:'center', gap:4 }}>
                View Story <ArrowUpRight size={13} />
              </span>
            </div>
          </div>
        ))}
      </div>
    </div>
  );
}

// ─── In-Grid Lead Gen Card ────────────────────────────────────────────────────
function InGridLeadCard({ onOpenQuote }) {
  const [ref, vis] = useReveal();
  return (
    <div
      ref={ref}
      className={`reveal ${vis ? 'in' : ''}`}
      style={{
        gridColumn:'1 / -1',
        background:'linear-gradient(135deg, #1E3A8A 0%, #1E40AF 60%, #2563EB 100%)',
        borderRadius:24,
        padding:'36px 40px',
      color:'#FFFFFF',
      display:'flex',
      flexWrap:'wrap',
      alignItems:'center',
      justifyContent:'space-between',
      gap:24,
      boxShadow:'0 20px 50px rgba(30,64,175,.25)',
      margin:'16px 0'
    }}>
      <div style={{ maxWidth:650 }}>
        <div className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.15em', color:'#93C5FD', fontWeight:700, marginBottom:8 }}>
          ✦ Ready to Build Your Solution?
        </div>
        <h3 className="display" style={{ fontSize:'clamp(1.8rem, 3.2vw, 2.5rem)', lineHeight:1.2, margin:'0 0 12px', color:'#FFFFFF' }}>
          Have a project in mind for your business?
        </h3>
        <p style={{ fontSize:15, color:'#DBEAFE', lineHeight:1.6, margin:'0 0 16px' }}>
          Whether you need a high-converting website, an automated web application, a mobile app, or custom business software, our senior engineers deliver on time and on budget.
        </p>
        <div style={{ display:'flex', flexWrap:'wrap', gap:16, fontSize:12.5, color:'#BFDBFE' }}>
          <span>✓ Free Architectural Consultation</span>
          <span>✓ Transparent Fixed-Price Quote</span>
          <span>✓ 180 Days Included Warranty</span>
        </div>
      </div>

      <div style={{ display:'flex', flexDirection:'column', gap:12, flexShrink:0 }}>
        <button
          onClick={() => onOpenQuote()}
          className="mono"
          style={{
            background:'#FFFFFF',
            color:'#1E40AF',
            padding:'14px 28px',
            borderRadius:99,
            fontSize:12.5,
            fontWeight:700,
            textTransform:'uppercase',
            letterSpacing:'0.08em',
            cursor:'pointer',
            border:'none',
            boxShadow:'0 8px 24px rgba(0,0,0,.15)',
            transition:'all .2s ease',
            display:'inline-flex',
            alignItems:'center',
            gap:8
          }}
          onMouseEnter={e => { e.currentTarget.style.transform = 'translateY(-2px)'; e.currentTarget.style.background = '#F0F7FF'; }}
          onMouseLeave={e => { e.currentTarget.style.transform = 'translateY(0)'; e.currentTarget.style.background = '#FFFFFF'; }}
        >
          Get a Free Project Consultation <ArrowUpRight size={16} />
        </button>

        <div style={{ display:'flex', gap:16, justifyContent:'center', fontSize:12, color:'#BFDBFE' }}>
          <a href="tel:+919933905503" style={{ color:'#BFDBFE', textDecoration:'none' }}>📞 +91 9933 905 503</a>
          <span>·</span>
          <a href="mailto:customer@techpenta.com" style={{ color:'#BFDBFE', textDecoration:'none' }}>✉️ Direct Inquiry</a>
        </div>
      </div>
    </div>
  );
}

// ─── Project Card Helper & Component ──────────────────────────────────────────
function getMockupAddress(p, isApp) {
  if (p.url) {
    let clean = String(p.url).trim().replace(/^(https?:)?\/\//i, '').replace(/\/$/, '');
    if (clean.includes('play.google.com')) {
      const slug = (p.client || p.title || 'app').toLowerCase().replace(/[^a-z0-9]/g, '');
      return `play.google.com/store/apps/${slug}`;
    }
    if (clean.includes('apps.apple.com')) {
      const slug = (p.client || p.title || 'app').toLowerCase().replace(/[^a-z0-9]/g, '');
      return `apps.apple.com/app/${slug}`;
    }
    // For normal web domains, strip lengthy path or parameters
    if (clean.length > 28) {
      const domain = clean.split('/')[0];
      return domain;
    }
    return clean;
  }

  // Realistic fallback address when no explicit URL is configured
  const slug = (p.client || p.title || 'solution').toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '');
  if (p.type === 'app' || isApp || /macbook|linux|windows|ios|android/i.test(p.platform || '')) {
    const plat = (p.platform || '').toLowerCase();
    if (plat.includes('mac')) return `drivault.app/macos`;
    if (plat.includes('linux')) return `drivault.app/linux`;
    if (plat.includes('win')) return `drivault.app/windows`;
    if (plat.includes('ios') || plat.includes('android')) return `${slug}.app · mobile`;
    return `${slug}.app`;
  }
  if (p.type === 'software' || /software|tool|saas/i.test(p.categories?.join(' ') || '')) {
    return `cloud.${slug}.io`;
  }
  if (p.type === 'logo' || p.categories?.includes('Brand & Logo')) {
    return `brand.${slug}.design`;
  }
  if (p.type === 'seo' || p.categories?.includes('SEO & Marketing')) {
    return `rankings.${slug}.analytics`;
  }
  return `${slug}.techpenta.com`;
}

function ProjectCard({ p, i, onSelect, onOpenQuote }) {
  const [ref, vis] = useReveal();
  const imgs = p.images?.length ? p.images : (p.image ? [p.image] : ['']);
  const isApp = p.categories?.includes('Mobile Apps') || p.type === 'app' || /macbook|linux|windows|ios|android/i.test(p.platform || '');
  const mockupAddress = getMockupAddress(p, isApp);
  const liveUrl = resolveFeatureUrl(p);

  return (
    <article
      ref={ref}
      className={`reveal ${vis?'in':''} project-card-interactive project-card-shimmer`}
      onClick={() => onSelect(p)}
      style={{
        cursor:'pointer',
        background:'#FFFFFF',
        borderRadius:20,
        border:'1.5px solid #DBEAFE',
        overflow:'hidden',
        boxShadow:'0 4px 20px rgba(30,64,175,.06)',
        display:'flex',
        flexDirection:'column',
        transitionDelay: `${(i % 4) * 80}ms`
      }}
    >
      {/* Mockup Top Window Chrome */}
      <div style={{ padding:'8px 12px', background:'#F8FAFC', borderBottom:'1px solid #E2E8F0', display:'flex', alignItems:'center', gap:8 }}>
        {/* Traffic Window Buttons */}
        <div style={{ display:'flex', gap:5, flexShrink:0 }}>
          {['#F87171','#FBBF24','#34D399'].map(c => (
            <span key={c} style={{ width:9, height:9, borderRadius:'50%', background:c, display:'inline-block' }} />
          ))}
        </div>

        {/* Address & Window Bar */}
        <div style={{
          flex:1,
          minWidth:120,
          background:'#FFFFFF',
          borderRadius:6,
          padding:'4px 10px',
          fontFamily:'Geist Mono,monospace',
          fontSize:9.5,
          color:'#475569',
          overflow:'hidden',
          textOverflow:'ellipsis',
          whiteSpace:'nowrap',
          border:'1px solid #E2E8F0',
          display:'flex',
          alignItems:'center',
          gap:5
        }}>
          <span style={{ fontSize:9, opacity:0.65 }}>🔒</span>
          <span style={{ overflow:'hidden', textOverflow:'ellipsis', whiteSpace:'nowrap' }}>
            {mockupAddress}
          </span>
        </div>

        {/* Single Status / Platform Badge on Right */}
        {p.platform ? (
          <span className="mono" style={{
            flexShrink:0,
            fontSize:9,
            color: /macbook|macos/i.test(p.platform) ? '#334155' : /linux/i.test(p.platform) ? '#92400E' : /windows/i.test(p.platform) ? '#0369A1' : '#6D28D9',
            background: /macbook|macos/i.test(p.platform) ? '#F1F5F9' : /linux/i.test(p.platform) ? '#FEF3C7' : /windows/i.test(p.platform) ? '#E0F2FE' : '#F5F3FF',
            border: '1px solid ' + (/macbook|macos/i.test(p.platform) ? '#CBD5E1' : /linux/i.test(p.platform) ? '#FDE68A' : /windows/i.test(p.platform) ? '#BAE6FD' : '#DDD6FE'),
            padding:'2px 8px',
            borderRadius:99,
            fontWeight:700,
            display:'inline-flex',
            alignItems:'center',
            gap:3,
            whiteSpace:'nowrap'
          }}>
            {/macbook|macos/i.test(p.platform) && ' '}
            {/linux/i.test(p.platform) && '🐧 '}
            {/windows/i.test(p.platform) && '⊞ '}
            {/ios|android/i.test(p.platform) && '📱 '}
            <span>{p.platform}</span>
          </span>
        ) : p.metrics?.performance ? (
          <span className="mono" style={{ flexShrink:0, fontSize:9, color:'#059669', background:'#ECFDF5', border:'1px solid #A7F3D0', padding:'2px 7px', borderRadius:99, fontWeight:700, whiteSpace:'nowrap' }}>
            ⚡ {p.metrics.performance}/100
          </span>
        ) : null}
      </div>

      {/* Visual Preview Carousel Area */}
      <div style={{ position:'relative', overflow:'hidden' }}>
        <Carousel images={imgs} aspectRatio={isApp && !p.categories?.includes('Websites') ? "68%" : "58%"} fit={isApp ? 'contain' : 'cover'} />
        
        {/* Floating Impact Pill */}
        {p.impact && (
          <div style={{
            position:'absolute',
            top:10,
            left:10,
            zIndex:7,
            background:'linear-gradient(135deg, #059669 0%, #047857 100%)',
            color:'#FFFFFF',
            padding:'4px 10px',
            borderRadius:99,
            fontSize:10,
            fontWeight:700,
            letterSpacing:'0.02em',
            boxShadow:'0 4px 12px rgba(5,150,105,.35)',
            display:'flex',
            alignItems:'center',
            gap:4
          }}>
            <span>🚀</span>
            <span>{p.impact}</span>
          </div>
        )}

        {/* Floating Industry Badge */}
        <div style={{
          position:'absolute',
          top:10,
          right:10,
          zIndex:7,
          background:'rgba(15,23,42,.82)',
          backdropFilter:'blur(8px)',
          border:'1px solid rgba(255,255,255,.15)',
          color:'#F8FAFC',
          padding:'3px 9px',
          borderRadius:99,
          fontSize:9,
          fontFamily:'Geist Mono,monospace',
          textTransform:'uppercase',
          letterSpacing:'0.08em',
          fontWeight:600
        }}>
          {p.industry || p.siteType}
        </div>

        {/* Floating Video Available Badge */}
        {p.videoUrl && (
          <div style={{
            position:'absolute',
            bottom:10,
            left:10,
            zIndex:7,
            background:'rgba(15,23,42,0.88)',
            backdropFilter:'blur(6px)',
            color:'#93C5FD',
            padding:'4px 9px',
            borderRadius:99,
            fontSize:9.5,
            fontWeight:700,
            border:'1px solid rgba(147,197,253,0.3)',
            boxShadow:'0 4px 12px rgba(0,0,0,.25)',
            display:'flex',
            alignItems:'center',
            gap:4
          }}>
            <span style={{ width:6, height:6, borderRadius:'50%', background:'#34D399', boxShadow:'0 0 6px #34D399' }} />
            <span>🎬 Video Demo</span>
          </div>
        )}

        {/* Floating Expand Icon */}
        <div
          title="Open Case Study"
          style={{
            position:'absolute',
            bottom:10,
            right:10,
            width:32,
            height:32,
            borderRadius:'50%',
            background:'rgba(255,255,255,.92)',
            backdropFilter:'blur(4px)',
            display:'flex',
            alignItems:'center',
            justifyContent:'center',
            zIndex:7,
            color:'#1E40AF',
            boxShadow:'0 4px 12px rgba(0,0,0,.15)',
            transition:'all .2s ease'
          }}
          onMouseEnter={e => { e.currentTarget.style.background = '#1E40AF'; e.currentTarget.style.color = '#fff'; }}
          onMouseLeave={e => { e.currentTarget.style.background = 'rgba(255,255,255,.92)'; e.currentTarget.style.color = '#1E40AF'; }}
        >
          <ArrowUpRight size={14} />
        </div>
      </div>

      {/* Card Body */}
      <div style={{ padding:'18px 20px 20px', display:'flex', flexDirection:'column', flex:1 }}>
        
        {/* Meta Header */}
        <div style={{ display:'flex', alignItems:'center', gap:7, marginBottom:8, flexWrap:'wrap' }}>
          <span className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#1E40AF', background:'#EFF6FF', border:'1px solid #DBEAFE', padding:'2px 8px', borderRadius:99, fontWeight:700, letterSpacing:'0.06em' }}>
            {p.displayType || p.siteType || 'Web Solution'}
          </span>
          {p.metrics?.performance && (
            <span className="mono" style={{ fontSize:9.5, color:'#059669', background:'#ECFDF5', border:'1px solid #A7F3D0', padding:'2px 6px', borderRadius:99, fontWeight:700 }}>
              ⚡ {p.metrics.performance}/100
            </span>
          )}
          <span style={{ color:'#CBD5E1' }}>·</span>
          <span className="mono" style={{ fontSize:10.5, color:'#64748B' }}>
            Client: {p.client || p.name || p.title}
          </span>
          <span style={{ color:'#CBD5E1' }}>·</span>
          <span className="mono" style={{ fontSize:10.5, color:'#94A3B8' }}>{p.year}</span>
        </div>

        {/* Project Title */}
        <h3 className="display" style={{ fontSize:21, color:'#0F172A', margin:'0 0 6px', lineHeight:1.25 }}>
          {p.displayTitle || p.title}
        </h3>

        {/* Business Summary */}
        <p style={{ fontSize:13, color:'#475569', lineHeight:1.5, margin:'0 0 14px' }}>
          {p.businessSummary || p.tagline}
        </p>

        {/* The Challenge & Our Solution (Designer-Grade Problem/Solution Box) */}
        <div style={{ background:'#F8FAFC', border:'1px solid #E2E8F0', borderRadius:12, padding:'11px 13px', marginBottom:14, display:'flex', flexDirection:'column', gap:8 }}>
          <div style={{ fontSize:12, lineHeight:1.45, display:'flex', alignItems:'flex-start', gap:8 }}>
            <span style={{ fontSize:9.5, padding:'2px 6px', borderRadius:4, background:'#FEE2E2', color:'#B91C1C', fontWeight:700, textTransform:'uppercase', letterSpacing:'0.04em', flexShrink:0, marginTop:1 }}>
              Problem
            </span>
            <span style={{ color:'#334155' }}>{p.challenge}</span>
          </div>
          <div style={{ fontSize:12, lineHeight:1.45, display:'flex', alignItems:'flex-start', gap:8, paddingTop:7, borderTop:'1px solid #F1F5F9' }}>
            <span style={{ fontSize:9.5, padding:'2px 6px', borderRadius:4, background:'#DCFCE7', color:'#15803D', fontWeight:700, textTransform:'uppercase', letterSpacing:'0.04em', flexShrink:0, marginTop:1 }}>
              Solution
            </span>
            <span style={{ color:'#334155' }}>{p.solution}</span>
          </div>
        </div>

        {/* Key Features Chips */}
        {p.keyFeatures && p.keyFeatures.length > 0 && (
          <div style={{ display:'flex', flexWrap:'wrap', gap:6, marginBottom:16 }}>
            {p.keyFeatures.slice(0, 3).map((feat, idx) => (
              <span
                key={idx}
                style={{
                  fontSize:11,
                  color:'#1E40AF',
                  background:'#EFF6FF',
                  border:'1px solid #DBEAFE',
                  borderRadius:6,
                  padding:'3px 8px',
                  fontWeight:500
                }}
              >
                ✓ {feat}
              </span>
            ))}
          </div>
        )}

        {/* Card Footer Actions */}
        <div style={{ display:'flex', alignItems:'center', justifyContent:'space-between', gap:8, paddingTop:14, borderTop:'1px solid #F1F5F9', marginTop:'auto', flexWrap:'wrap' }}>
          <button
            onClick={(e) => { e.stopPropagation(); onSelect(p); }}
            className="mono"
            style={{
              display:'inline-flex',
              alignItems:'center',
              gap:6,
              background:'#1E40AF',
              color:'#FFFFFF',
              border:'none',
              padding:'8px 16px',
              borderRadius:99,
              fontSize:11,
              fontWeight:600,
              textTransform:'uppercase',
              letterSpacing:'0.06em',
              cursor:'pointer',
              transition:'background .15s'
            }}
            onMouseEnter={e => e.currentTarget.style.background = '#1D4ED8'}
            onMouseLeave={e => e.currentTarget.style.background = '#1E40AF'}
          >
            Explore Story <ArrowUpRight size={13} />
          </button>

          <div style={{ display:'flex', alignItems:'center', gap:6 }}>
            {liveUrl && (
              <a
                href={liveUrl}
                target="_blank"
                rel="noopener noreferrer"
                onClick={e => e.stopPropagation()}
                title={isApp ? 'Open App Store / Download' : 'Open Live Website'}
                className="mono"
                style={{
                  display:'inline-flex',
                  alignItems:'center',
                  gap:4,
                  padding:'7px 11px',
                  borderRadius:99,
                  border:'1px solid #BFDBFE',
                  color:'#1E40AF',
                  fontSize:10.5,
                  textDecoration:'none',
                  fontWeight:600,
                  transition:'all .15s'
                }}
                onMouseEnter={e => { e.currentTarget.style.background = '#EFF6FF'; e.currentTarget.style.borderColor = '#2563EB'; }}
                onMouseLeave={e => { e.currentTarget.style.background = 'transparent'; e.currentTarget.style.borderColor = '#BFDBFE'; }}
              >
                <Globe size={12} /> {isApp ? 'Live App' : 'Live Site'}
              </a>
            )}
            <button
              onClick={(e) => { e.stopPropagation(); onOpenQuote && onOpenQuote(p); }}
              title="Want a similar solution for your business?"
              className="mono"
              style={{
                background:'transparent',
                border:'1px solid #BFDBFE',
                color:'#1E40AF',
                padding:'7px 12px',
                borderRadius:99,
                fontSize:10.5,
                fontWeight:600,
                cursor:'pointer',
                transition:'all .15s'
              }}
              onMouseEnter={e => { e.currentTarget.style.background = '#EFF6FF'; e.currentTarget.style.borderColor = '#3B82F6'; }}
              onMouseLeave={e => { e.currentTarget.style.background = 'transparent'; e.currentTarget.style.borderColor = '#BFDBFE'; }}
            >
              Want Similar?
            </button>
          </div>
        </div>

      </div>
    </article>
  );
}

// ─── Trust & Process Section (Bottom of Work Section) ─────────────────────────
function TrustProcessSection({ onOpenQuote }) {
  const [ref, vis] = useReveal();
  return (
    <div ref={ref} className={`reveal ${vis ? 'in' : ''}`} style={{ marginTop:60, borderTop:'1.5px solid #DBEAFE', paddingTop:50 }}>
      {/* 4 Pillars of Trust */}
      <div style={{ marginBottom:48 }}>
        <div style={{ textAlign:'center', maxWidth:640, margin:'0 auto 36px' }}>
          <div className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.15em', color:'#2563EB', fontWeight:700, marginBottom:8 }}>
            ✦ Why Choose TechPenta
          </div>
          <h3 className="display" style={{ fontSize:'clamp(1.8rem,3.4vw,2.6rem)', lineHeight:1.35, color:'#0F172A', margin:'0 0 12px' }}>
            Built for <span className="display-it" style={{ color:'#1E40AF' }}>long-term business success</span>.
          </h3>
          <p style={{ fontSize:14.5, color:'#64748B', lineHeight:1.6 }}>
            We understand that launching a digital product is a major investment. Here is how we ensure your project succeeds without friction.
          </p>
        </div>

        <div style={{ display:'grid', gridTemplateColumns:'repeat(auto-fit, minmax(250px, 1fr))', gap:22 }}>
          <div style={{ background:'#FFFFFF', border:'1px solid #DBEAFE', borderRadius:18, padding:24, boxShadow:'0 4px 16px rgba(30,64,175,.04)' }}>
            <div style={{ width:44, height:44, borderRadius:12, background:'#EFF6FF', color:'#1E40AF', display:'flex', alignItems:'center', justifyContent:'center', marginBottom:16 }}>
              <Rocket size={22} />
            </div>
            <h4 style={{ fontSize:16, fontWeight:700, color:'#0F172A', marginBottom:8 }}>Business-First Strategy</h4>
            <p style={{ fontSize:13, color:'#475569', lineHeight:1.5, margin:0 }}>
              We prioritize customer conversions, ease of use, and speed over complex jargon that doesn't help your bottom line.
            </p>
          </div>

          <div style={{ background:'#FFFFFF', border:'1px solid #DBEAFE', borderRadius:18, padding:24, boxShadow:'0 4px 16px rgba(30,64,175,.04)' }}>
            <div style={{ width:44, height:44, borderRadius:12, background:'#ECFDF5', color:'#059669', display:'flex', alignItems:'center', justifyContent:'center', marginBottom:16 }}>
              <Shield size={22} />
            </div>
            <h4 style={{ fontSize:16, fontWeight:700, color:'#0F172A', marginBottom:8 }}>180 Days Included Warranty</h4>
            <p style={{ fontSize:13, color:'#475569', lineHeight:1.5, margin:0 }}>
              Every single project comes with 6 months of complimentary bug fixing, security updates, and technical maintenance.
            </p>
          </div>

          <div style={{ background:'#FFFFFF', border:'1px solid #DBEAFE', borderRadius:18, padding:24, boxShadow:'0 4px 16px rgba(30,64,175,.04)' }}>
            <div style={{ width:44, height:44, borderRadius:12, background:'#FEF3C7', color:'#D97706', display:'flex', alignItems:'center', justifyContent:'center', marginBottom:16 }}>
              <BadgeCheck size={22} />
            </div>
            <h4 style={{ fontSize:16, fontWeight:700, color:'#0F172A', marginBottom:8 }}>Fixed Pricing & Milestones</h4>
            <p style={{ fontSize:13, color:'#475569', lineHeight:1.5, margin:0 }}>
              No surprises or hidden fees. We define clear deliverables and you only pay as each verified milestone is approved.
            </p>
          </div>

          <div style={{ background:'#FFFFFF', border:'1px solid #DBEAFE', borderRadius:18, padding:24, boxShadow:'0 4px 16px rgba(30,64,175,.04)' }}>
            <div style={{ width:44, height:44, borderRadius:12, background:'#F5F3FF', color:'#7C3AED', display:'flex', alignItems:'center', justifyContent:'center', marginBottom:16 }}>
              <Layers size={22} />
            </div>
            <h4 style={{ fontSize:16, fontWeight:700, color:'#0F172A', marginBottom:8 }}>100% Code & Asset Ownership</h4>
            <p style={{ fontSize:13, color:'#475569', lineHeight:1.5, margin:0 }}>
              You own full rights to your intellectual property, designs, database, and source code. No vendor lock-in ever.
            </p>
          </div>
        </div>
      </div>

      {/* 4 Steps Journey */}
      <div style={{ background:'#FFFFFF', border:'1.5px solid #DBEAFE', borderRadius:24, padding:'36px 32px', marginBottom:36, boxShadow:'0 10px 30px rgba(30,64,175,.06)' }}>
        <div style={{ textAlign:'center', marginBottom:32 }}>
          <div className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.12em', color:'#2563EB', fontWeight:700, marginBottom:6 }}>
            ✦ How We Work Together
          </div>
          <h3 className="display" style={{ fontSize:24, lineHeight:1.3, color:'#0F172A', margin:0 }}>
            Our simple 4-step journey to launch.
          </h3>
        </div>

        <div style={{ display:'grid', gridTemplateColumns:'repeat(auto-fit, minmax(220px, 1fr))', gap:20 }}>
          <div style={{ position:'relative', padding:'16px' }}>
            <div className="mono" style={{ fontSize:26, fontWeight:800, color:'#DBEAFE', marginBottom:8 }}>01</div>
            <h5 style={{ fontSize:15, fontWeight:700, color:'#0F172A', marginBottom:6 }}>Free Consultation & Scope</h5>
            <p style={{ fontSize:12.5, color:'#64748B', lineHeight:1.5, margin:0 }}>
              We discuss your goals, target audience, and business requirements to deliver a fixed-scope roadmap.
            </p>
          </div>

          <div style={{ position:'relative', padding:'16px' }}>
            <div className="mono" style={{ fontSize:26, fontWeight:800, color:'#DBEAFE', marginBottom:8 }}>02</div>
            <h5 style={{ fontSize:15, fontWeight:700, color:'#0F172A', marginBottom:6 }}>Interactive UI/UX Design</h5>
            <p style={{ fontSize:12.5, color:'#64748B', lineHeight:1.5, margin:0 }}>
              You preview and approve every screen layout and user flow before any coding begins.
            </p>
          </div>

          <div style={{ position:'relative', padding:'16px' }}>
            <div className="mono" style={{ fontSize:26, fontWeight:800, color:'#DBEAFE', marginBottom:8 }}>03</div>
            <h5 style={{ fontSize:15, fontWeight:700, color:'#0F172A', marginBottom:6 }}>Agile Build & QA</h5>
            <p style={{ fontSize:12.5, color:'#64748B', lineHeight:1.5, margin:0 }}>
              Clean, scalable engineering tested across iOS, Android, tablets, and modern desktop browsers.
            </p>
          </div>

          <div style={{ position:'relative', padding:'16px' }}>
            <div className="mono" style={{ fontSize:26, fontWeight:800, color:'#DBEAFE', marginBottom:8 }}>04</div>
            <h5 style={{ fontSize:15, fontWeight:700, color:'#0F172A', marginBottom:6 }}>Go-Live & 180-Day Warranty</h5>
            <p style={{ fontSize:12.5, color:'#64748B', lineHeight:1.5, margin:0 }}>
              Smooth deployment with domain setup, staff training, and 6 months of dedicated technical backup.
            </p>
          </div>
        </div>
      </div>

      {/* Final Lead Gen Banner */}
      <div style={{
        background:'#EFF6FF',
        border:'1.5px solid #BFDBFE',
        borderRadius:20,
        padding:'32px 36px',
        textAlign:'center',
        boxShadow:'0 8px 24px rgba(30,64,175,.06)'
      }}>
        <h3 className="display" style={{ fontSize:'clamp(1.6rem, 2.8vw, 2.2rem)', lineHeight:1.3, color:'#0F172A', margin:'0 0 10px' }}>
          Ready to build something <span className="display-it" style={{ color:'#1E40AF' }}>exceptional</span> for your business?
        </h3>
        <p style={{ fontSize:14.5, color:'#475569', maxWidth:580, margin:'0 auto 20px', lineHeight:1.6 }}>
          Schedule a free 30-minute consultation with our technology team. We will review your goals and provide an honest estimate with no obligations.
        </p>
        <div style={{ display:'flex', gap:14, justifyContent:'center', flexWrap:'wrap', alignItems:'center' }}>
          <button
            onClick={() => onOpenQuote()}
            className="btn-primary mono"
            style={{
              display:'inline-flex',
              alignItems:'center',
              justifyContent:'center',
              gap:8,
              padding:'13px 26px',
              borderRadius:99,
              fontSize:12,
              fontWeight:700,
              textTransform:'uppercase',
              letterSpacing:'0.08em',
              cursor:'pointer',
              whiteSpace:'nowrap',
              lineHeight:1
            }}
          >
            <span>Get a Free Project Consultation</span>
            <ArrowUpRight size={15} strokeWidth={2.4} />
          </button>
          <a
            href="tel:+919933905503"
            className="mono"
            style={{
              display:'inline-flex',
              alignItems:'center',
              justifyContent:'center',
              gap:8,
              padding:'13px 24px',
              borderRadius:99,
              border:'1.5px solid #BFDBFE',
              background:'#FFFFFF',
              color:'#1E40AF',
              fontSize:12,
              fontWeight:700,
              textDecoration:'none',
              whiteSpace:'nowrap',
              lineHeight:1,
              transition:'all .2s ease'
            }}
            onMouseEnter={e => { e.currentTarget.style.background = '#EFF6FF'; e.currentTarget.style.borderColor = '#1E40AF'; }}
            onMouseLeave={e => { e.currentTarget.style.background = '#FFFFFF'; e.currentTarget.style.borderColor = '#BFDBFE'; }}
          >
            <Phone size={14} strokeWidth={2.2} />
            <span>Call +91 9933 905 503</span>
          </a>
        </div>
      </div>
    </div>
  );
}

// ─── Tech stack brand data ────────────────────────────────────────────────────
const TECH_BRANDS = {
  'php':           { slug:'php',           hex:'777BB4' },
  'laravel':       { slug:'laravel',       hex:'FF2D20' },
  'python':        { slug:'python',        hex:'3776AB' },
  'django':        { slug:'django',        hex:'092E20' },
  'react':         { slug:'react',         hex:'61DAFB' },
  'angular':       { slug:'angular',       hex:'DD0031' },
  'vue':           { slug:'vuedotjs',      hex:'4FC08D' },
  'vue.js':        { slug:'vuedotjs',      hex:'4FC08D' },
  'react native':  { slug:'react',         hex:'61DAFB' },
  'flutter':       { slug:'flutter',       hex:'02569B' },
  'ios':           { slug:'apple',         hex:'000000' },
  'android':       { slug:'android',       hex:'3DDC84' },
  'wordpress':     { slug:'wordpress',     hex:'21759B' },
  'woocommerce':   { slug:'woocommerce',   hex:'96588A' },
  'shopify':       { slug:'shopify',       hex:'7AB55C' },
  'joomla':        { slug:'joomla',        hex:'5091CD' },
  'node':          { slug:'nodedotjs',     hex:'5FA04E' },
  'node.js':       { slug:'nodedotjs',     hex:'5FA04E' },
  'nodejs':        { slug:'nodedotjs',     hex:'5FA04E' },
  'next':          { slug:'nextdotjs',     hex:'000000' },
  'next.js':       { slug:'nextdotjs',     hex:'000000' },
  'typescript':    { slug:'typescript',    hex:'3178C6' },
  'javascript':    { slug:'javascript',    hex:'F7DF1E' },
  'mysql':         { slug:'mysql',         hex:'4479A1' },
  'postgresql':    { slug:'postgresql',    hex:'4169E1' },
  'mongodb':       { slug:'mongodb',       hex:'47A248' },
  'firebase':      { slug:'firebase',      hex:'FFCA28' },
  'aws':           { slug:'amazonwebservices', hex:'232F3E' },
  'magento':       { slug:'magento',       hex:'EE672F' },
  'drupal':        { slug:'drupal',        hex:'0678BE' },
  'tailwind':      { slug:'tailwindcss',   hex:'06B6D4' },
  'tailwindcss':   { slug:'tailwindcss',   hex:'06B6D4' },
};

function TechChip({ name }) {
  const brand = TECH_BRANDS[(name||'').toLowerCase()];
  const hex = brand?.hex || '1E40AF';
  const src = brand ? `https://cdn.simpleicons.org/${brand.slug}/${hex}` : null;
  return (
    <span className="tech-chip"
      onMouseEnter={e => { e.currentTarget.style.borderColor = `#${hex}`; e.currentTarget.style.boxShadow = `0 8px 22px -8px #${hex}66`; e.currentTarget.style.background = `#${hex}0f`; }}
      onMouseLeave={e => { e.currentTarget.style.borderColor = '#E2E8F0'; e.currentTarget.style.boxShadow = 'none'; e.currentTarget.style.background = '#fff'; }}>
      {src
        ? <FadeImg src={src} alt="" width={18} height={18} />
        : <span style={{ width:8, height:8, borderRadius:'50%', background:`#${hex}`, display:'inline-block' }} />}
      <span>{name}</span>
    </span>
  );
}

// ─── Services ─────────────────────────────────────────────────────────────────
function serviceMeta(title) {
  const n = (title || '').toLowerCase();
  if (n.includes('website') || n.includes('web ')) return { Icon: Globe, accent:'#2563EB', tint:'#DBEAFE', soft:'#EFF6FF' };
  if (n.includes('mobile') || n.includes('app')) return { Icon: Smartphone, accent:'#7C3AED', tint:'#EDE9FE', soft:'#F5F3FF' };
  if (n.includes('logo') || n.includes('brand') || n.includes('design')) return { Icon: Palette, accent:'#DB2777', tint:'#FCE7F3', soft:'#FDF2F8' };
  if (n.includes('seo') || n.includes('marketing') || n.includes('digital')) return { Icon: TrendingUp, accent:'#059669', tint:'#D1FAE5', soft:'#ECFDF5' };
  if (n.includes('ecommerce') || n.includes('shop')) return { Icon: ShoppingBag, accent:'#D97706', tint:'#FEF3C7', soft:'#FFFBEB' };
  if (n.includes('content') || n.includes('copy')) return { Icon: Code, accent:'#0284C7', tint:'#E0F2FE', soft:'#F0F9FF' };
  return { Icon: Zap, accent:'#1E40AF', tint:'#DBEAFE', soft:'#EFF6FF' };
}

function ServiceRow({ s, i }) {
  const { Icon, accent, tint, soft } = serviceMeta(s.t);
  return (
    <div className="svc-row" style={{ color:accent }}>
      <div className="svc-badge" style={{ background:soft, borderColor:tint, color:accent }}>
        <Icon size={22} color={accent} strokeWidth={2.2} />
        <span className="svc-badge-num" style={{ color:accent, padding:'0 6px' }}>{String(i+1).padStart(2,'0')}</span>
      </div>
      <div style={{ flex:1, minWidth:0, position:'relative', zIndex:1 }}>
        <div className="display" style={{ fontSize:17, color:'#0F172A', fontWeight:600, marginBottom:3, lineHeight:1.25 }}>{s.t}</div>
        <div style={{ fontSize:13, color:'#64748B', lineHeight:1.5 }}>{s.d}</div>
      </div>
      <div className="svc-arrow">
        <ArrowUpRight size={16} strokeWidth={2.4} />
      </div>
    </div>
  );
}

function ServicesSection({ data }) {
  const [ref, vis] = useReveal();
  return (
    <section id="services" style={{ padding:'80px 5%', background:'#fff', borderTop:'1px solid #DBEAFE' }}>
      <div className="resp-2col" style={{ maxWidth:1200, margin:'0 auto' }}>
        <div ref={ref} className={`reveal ${vis?'in':''}`}>
          <div className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.15em', color:'#3B82F6', marginBottom:10 }}>§ What We Do</div>
          <h2 className="display" style={{ fontSize:'clamp(2rem,4vw,3.5rem)', marginBottom:20, color:'#0F172A' }}>Full-stack <span className="display-it" style={{ color:'#1E40AF' }}>delivery</span>.</h2>
          <p style={{ color:'#475569', lineHeight:1.7, marginBottom:28, fontSize:15 }}>From the first wireframe to post-launch SEO, Techpenta is a one-stop studio.</p>
          <div>
            {(data.services||[]).map((s,i) => <ServiceRow key={i} s={s} i={i} />)}
          </div>
        </div>
        <div className={`reveal ${vis?'in':''} delay-200`}>
          <div className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.15em', color:'#3B82F6', marginBottom:10 }}>§ Tech Stack</div>
          <h2 className="display" style={{ fontSize:'clamp(2rem,4vw,3.5rem)', marginBottom:20, color:'#0F172A' }}>Tools <span className="display-it" style={{ color:'#1E40AF' }}>we use</span>.</h2>
          <div style={{ display:'flex', flexWrap:'wrap', gap:8, marginBottom:28 }}>
            {(data.techStack||[]).map(t => <TechChip key={t} name={t} />)}
          </div>
          <div style={{ padding:24, background:'linear-gradient(135deg,#EFF6FF,#DBEAFE)', borderRadius:16, border:'1px solid #BFDBFE' }}>
            <div className="mono" style={{ fontSize:10, textTransform:'uppercase', letterSpacing:'0.12em', color:'#3B82F6', marginBottom:8 }}>Support promise</div>
            <div className="display" style={{ fontSize:'2.5rem', marginBottom:6, color:'#0F172A' }}>{data.support?.days} days <span className="display-it" style={{ color:'#1E40AF' }}>free</span></div>
            <div style={{ fontSize:13, color:'#475569' }}>{data.support?.desc}</div>
          </div>
        </div>
      </div>
    </section>
  );
}

// ─── Why Choose Us ────────────────────────────────────────────────────────────
const WHY_US = [
  { icon: Award,         title: '18+ Years of Experience',     desc: 'A seasoned team that has shipped through multiple web eras — we bring patterns, not pitfalls.', accent:'#D97706', tint:'#FEF3C7', soft:'#FFFBEB' },
  { icon: Users,         title: '98% Client Retention',        desc: 'Clients stay because we keep shipping — long-term partnerships, not one-off projects.',          accent:'#059669', tint:'#D1FAE5', soft:'#ECFDF5' },
  { icon: BadgeCheck,    title: '2500+ Projects Delivered',    desc: 'From startup MVPs to enterprise platforms, across a dozen industries worldwide.',               accent:'#2563EB', tint:'#DBEAFE', soft:'#EFF6FF' },
  { icon: Headphones,    title: '24 × 7 Technical Support',    desc: 'Real engineers, not a ticket queue. We monitor, patch, and respond — even at 3 a.m.',           accent:'#7C3AED', tint:'#EDE9FE', soft:'#F5F3FF' },
  { icon: Shield,        title: '180 Days Free Support',       desc: 'Every build ships with six months of complimentary technical backup at no extra cost.',         accent:'#DB2777', tint:'#FCE7F3', soft:'#FDF2F8' },
  { icon: Briefcase,     title: 'Dedicated Project Manager',   desc: 'One point of contact who owns your timeline, quality, and communication end-to-end.',           accent:'#0D9488', tint:'#CCFBF1', soft:'#F0FDFA' },
  { icon: Wallet,        title: 'Transparent Pricing',         desc: 'Fixed-scope estimates with no hidden fees. Change requests are scoped openly before any work.', accent:'#CA8A04', tint:'#FEF9C3', soft:'#FEFCE8' },
  { icon: Clock,         title: 'On-Time Delivery',            desc: 'Milestone-driven sprints with weekly demos — you always know what is landing and when.',        accent:'#0284C7', tint:'#E0F2FE', soft:'#F0F9FF' },
  { icon: Target,        title: 'SEO-First Approach',          desc: 'Performance, schema, and content structure baked in from day one — not patched on later.',     accent:'#E11D48', tint:'#FFE4E6', soft:'#FFF1F2' },
  { icon: Layers,        title: 'Cross-Platform Expertise',    desc: 'WordPress, Laravel, React, React Native, Flutter, iOS, Android — one studio, every stack.',    accent:'#9333EA', tint:'#F3E8FF', soft:'#FAF5FF' },
];

function useTypewriter(items, { typeMs = 55, pauseMs = 1400, deleteMs = 28 } = {}) {
  const [index, setIndex] = useState(0);
  const [text, setText] = useState('');
  const [phase, setPhase] = useState('typing'); // typing | pausing | deleting
  useEffect(() => {
    if (!items || items.length === 0) return;
    const current = items[index] || '';
    let t;
    if (phase === 'typing') {
      if (text.length < current.length) {
        t = setTimeout(() => setText(current.slice(0, text.length + 1)), typeMs);
      } else {
        t = setTimeout(() => setPhase('pausing'), 40);
      }
    } else if (phase === 'pausing') {
      t = setTimeout(() => setPhase('deleting'), pauseMs);
    } else if (phase === 'deleting') {
      if (text.length > 0) {
        t = setTimeout(() => setText(text.slice(0, -1)), deleteMs);
      } else {
        setPhase('typing');
        setIndex(i => (i + 1) % items.length);
      }
    }
    return () => clearTimeout(t);
  }, [text, phase, index, items, typeMs, pauseMs, deleteMs]);
  return { text, index, phase };
}

function WhyUsCard({ item, i, active }) {
  const [ref, vis] = useReveal();
  const Icon = item.icon;
  const styleVars = {
    '--why-accent': item.accent,
    '--why-accent-shadow': item.accent + '55',
    '--why-tint': item.tint,
    '--why-soft': item.soft,
    '--why-grad': `linear-gradient(135deg, ${item.soft} 0%, ${item.tint} 100%)`,
  };
  return (
    <div ref={ref} className={`why-card reveal ${vis?'in':''} ${active?'active':''}`} style={{ ...styleVars, transitionDelay:`${i*50}ms` }}>
      <span className="why-num">{String(i+1).padStart(2,'0')}</span>
      <div style={{ display:'flex', alignItems:'flex-start', gap:16, marginBottom:10 }}>
        <div className="why-badge">
          <span className="why-badge-glow" />
          <Icon size={24} color={item.accent} strokeWidth={2.2} />
        </div>
        <div style={{ flex:1, minWidth:0, paddingTop:4, paddingRight:46 }}>
          <div className="display" style={{ fontSize:17, color:'#0F172A', fontWeight:600, lineHeight:1.25 }}>{item.title}</div>
        </div>
      </div>
      <p style={{ fontSize:13.5, color:'#64748B', lineHeight:1.6, marginLeft:70, marginRight:10 }}>{item.desc}</p>
      <div className="why-arrow"><ArrowUpRight size={14} strokeWidth={2.5} color="#fff" /></div>
    </div>
  );
}

function WhyUsSection() {
  const [ref, vis] = useReveal();
  const titles = WHY_US.map(w => w.title);
  const { text, index } = useTypewriter(titles);
  const activeAccent = WHY_US[index].accent;
  return (
    <section id="why-us" style={{ padding:'96px 5%', borderTop:'1px solid #DBEAFE', background:'linear-gradient(180deg,#FFFFFF 0%,#F8FAFF 50%,#FFFFFF 100%)', position:'relative', overflow:'hidden' }}>
      <div className="why-grid-bg" />
      <div className="blob anim-floatAlt" style={{ width:360, height:360, background:'#6366F1', top:-120, left:-100, opacity:.08 }} />
      <div className="blob anim-float" style={{ width:320, height:320, background:'#EC4899', bottom:-100, right:-80, opacity:.07 }} />
      <div style={{ maxWidth:1200, margin:'0 auto', position:'relative', zIndex:1 }}>
        <div ref={ref} className={`reveal ${vis?'in':''}`} style={{ textAlign:'center', marginBottom:48, maxWidth:820, marginLeft:'auto', marginRight:'auto' }}>
          <div style={{ display:'inline-flex', alignItems:'center', gap:8, padding:'6px 14px', background:'#fff', border:'1px solid #DBEAFE', borderRadius:99, marginBottom:18 }}>
            <Sparkles size={13} color="#1E40AF" />
            <span className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.15em', color:'#1E40AF', fontWeight:600 }}>Why Choose Us</span>
          </div>
          <h2 className="display" style={{ fontSize:'clamp(2rem,4.5vw,3.6rem)', color:'#0F172A', lineHeight:1.08, marginBottom:20 }}>
            <span>Ten reasons teams pick </span>
            <span className="display-it" style={{ background:'linear-gradient(90deg,#1E40AF,#7C3AED,#DB2777)', WebkitBackgroundClip:'text', WebkitTextFillColor:'transparent', backgroundClip:'text' }}>Techpenta</span>
            <span>.</span>
          </h2>
          <div aria-live="polite" style={{ minHeight:56, display:'flex', alignItems:'center', justifyContent:'center', marginBottom:14, padding:'0 12px' }}>
            <div className="resp-typewriter-chip" style={{ display:'inline-flex', alignItems:'center', gap:12, padding:'10px 20px 10px 14px', background:'#fff', border:`1.5px solid ${activeAccent}`, borderRadius:99, boxShadow:`0 10px 30px -12px ${activeAccent}66`, transition:'border-color .35s, box-shadow .35s' }}>
              <span style={{ width:30, height:30, borderRadius:'50%', background:activeAccent+'1a', display:'flex', alignItems:'center', justifyContent:'center', flexShrink:0, transition:'background .35s' }}>
                {(() => { const Ic = WHY_US[index].icon; return <Ic size={15} color={activeAccent} strokeWidth={2.4} />; })()}
              </span>
              <span className="mono tw-label" style={{ fontSize:10, textTransform:'uppercase', letterSpacing:'0.14em', color:'#94A3B8', fontWeight:600 }}>Now</span>
              <span className="tw-text" style={{ fontSize:15, fontWeight:600, color:activeAccent, whiteSpace:'nowrap', overflow:'hidden', textOverflow:'ellipsis', transition:'color .35s' }}>{text}</span>
              <span className="type-caret" style={{ background:activeAccent, height:'1em', flexShrink:0, transition:'background .35s' }} />
            </div>
          </div>
          <p style={{ fontSize:15.5, color:'#64748B', lineHeight:1.65 }}>We are small enough to care, large enough to ship. Here is what that looks like in practice.</p>
        </div>
        <div style={{ display:'grid', gridTemplateColumns:'repeat(auto-fit,minmax(320px,1fr))', gap:16 }}>
          {WHY_US.map((item, i) => <WhyUsCard key={item.title} item={item} i={i} active={i===index} />)}
        </div>
      </div>
    </section>
  );
}

// ─── Industries ───────────────────────────────────────────────────────────────
function GrowthIcon({ size = 108 }) {
  return (
    <svg className="growth-icon" width={size} height={size} viewBox="0 0 96 80" fill="none" aria-hidden="true" style={{ flexShrink:0 }}>
      <defs>
        <linearGradient id="gi-b1" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stopColor="#93C5FD"/><stop offset="1" stopColor="#60A5FA"/></linearGradient>
        <linearGradient id="gi-b2" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stopColor="#60A5FA"/><stop offset="1" stopColor="#3B82F6"/></linearGradient>
        <linearGradient id="gi-b3" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stopColor="#3B82F6"/><stop offset="1" stopColor="#1E40AF"/></linearGradient>
        <linearGradient id="gi-b4" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stopColor="#1E40AF"/><stop offset="1" stopColor="#0F1D3E"/></linearGradient>
        <linearGradient id="gi-trend" x1="0" y1="1" x2="1" y2="0"><stop offset="0" stopColor="#60A5FA"/><stop offset="1" stopColor="#1E40AF"/></linearGradient>
        <radialGradient id="gi-base" cx="50%" cy="50%" r="50%"><stop offset="0" stopColor="#3B82F6" stopOpacity=".35"/><stop offset="1" stopColor="#3B82F6" stopOpacity="0"/></radialGradient>
      </defs>

      {/* soft base glow */}
      <ellipse className="base-glow" cx="48" cy="72" rx="44" ry="6" fill="url(#gi-base)" />

      {/* baseline */}
      <line x1="4" y1="68" x2="92" y2="68" stroke="#DBEAFE" strokeWidth="1.5" strokeLinecap="round" strokeDasharray="2 3" />

      {/* 4 ascending bars (startup → enterprise) */}
      <rect className="bar b1" x="8"  y="48" width="14" height="20" rx="3" fill="url(#gi-b1)" />
      <rect className="bar b2" x="28" y="38" width="14" height="30" rx="3" fill="url(#gi-b2)" />
      <rect className="bar b3" x="48" y="26" width="14" height="42" rx="3" fill="url(#gi-b3)" />
      <rect className="bar b4" x="68" y="12" width="14" height="56" rx="3" fill="url(#gi-b4)" />

      {/* rising trend line */}
      <path className="trend" d="M8 64 L28 46 L48 34 L68 22 L88 10" stroke="url(#gi-trend)" strokeWidth="2.5" strokeLinecap="round" strokeLinejoin="round" fill="none" />

      {/* glowing dot travels along the trend */}
      <circle className="trend-dot" r="3.2" fill="#fff" stroke="#1E40AF" strokeWidth="1.5" />

      {/* sparkles near the peak */}
      <g fill="#FBBF24">
        <path className="spark s1" d="M88 6 l1.4 3 3 1.4 -3 1.4 -1.4 3 -1.4 -3 -3 -1.4 3 -1.4 z" />
        <path className="spark s2" d="M80 2 l.9 2 2 .9 -2 .9 -.9 2 -.9 -2 -2 -.9 2 -.9 z" opacity=".85" />
        <path className="spark s3" d="M92 18 l.8 1.7 1.7 .8 -1.7 .8 -.8 1.7 -.8 -1.7 -1.7 -.8 1.7 -.8 z" opacity=".75" />
      </g>
    </svg>
  );
}

function IndustriesSection({ data }) {
  const [ref, vis] = useReveal();
  const count = (data.industries || []).length;
  const [ballCount, setBallCount] = useState(() => {
    if (typeof window === 'undefined') return 72;
    if (window.innerWidth < 480) return 28;
    if (window.innerWidth < 768) return 40;
    if (window.innerWidth < 1280) return 56;
    return 72;
  });
  const [isMobile, setIsMobile] = useState(() => typeof window !== 'undefined' && window.innerWidth < 768);
  useEffect(() => {
    const onR = () => {
      const w = window.innerWidth;
      setBallCount(w < 480 ? 28 : w < 768 ? 40 : w < 1280 ? 56 : 72);
      setIsMobile(w < 768);
    };
    let t;
    const debounced = () => { clearTimeout(t); t = setTimeout(onR, 250); };
    window.addEventListener('resize', debounced);
    return () => { window.removeEventListener('resize', debounced); clearTimeout(t); };
  }, []);
  const industryLabels = useMemo(() => data.industries || [], [data.industries]);
  return (
    <section id="industries" style={{ padding:'96px 5%', borderTop:'1px solid #DBEAFE', position:'relative', overflow:'hidden', background:'linear-gradient(180deg,#FFFFFF 0%,#F8FAFF 100%)' }}>
      <div aria-hidden="true" style={{ position:'absolute', inset:0, zIndex:0 }}>
        <Suspense fallback={null}>
          <Ballpit key={`${ballCount}-${isMobile?'m':'d'}`} count={ballCount} labels={industryLabels} colors={["#2563EB","#3B82F6","#1D4ED8","#1E40AF","#4F46E5","#6366F1","#4338CA","#0EA5E9","#0284C7","#1E3A8A","#3730A3","#0369A1"]} followCursor={true} gravity={0.35} minSize={isMobile ? 0.3 : 0.6} maxSize={isMobile ? 0.55 : 1.1} size0={isMobile ? 0.5 : 1.0} />
        </Suspense>
      </div>
      <div style={{ maxWidth:1200, margin:'0 auto', position:'relative', zIndex:1 }}>
        <div ref={ref} className={`reveal ind-header ${vis?'in':''}`} style={{ marginBottom:44, display:'flex', alignItems:'center', gap:28, flexWrap:'wrap' }}>
          <GrowthIcon size={120} />
          <div style={{ flex:'1 1 300px', minWidth:0 }}>
            <div style={{ display:'flex', alignItems:'center', gap:10, marginBottom:14, flexWrap:'wrap' }}>
              <span className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.15em', color:'#3B82F6' }}>§ Industries Served</span>
              <span className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.14em', color:'#1E40AF', background:'#fff', border:'1px solid #DBEAFE', padding:'3px 10px', borderRadius:99, fontWeight:600, display:'inline-flex', alignItems:'center', gap:6 }}>
                <span style={{ width:6, height:6, borderRadius:'50%', background:'#1E40AF' }} /> {count} Sectors
              </span>
            </div>
            <h2 className="display" style={{ fontSize:'clamp(2rem,4.5vw,3.8rem)', color:'#0F172A', lineHeight:1.05 }}>From startups to <span className="display-it" style={{ background:'linear-gradient(90deg,#1E40AF,#3B82F6,#60A5FA)', WebkitBackgroundClip:'text', WebkitTextFillColor:'transparent', backgroundClip:'text' }}>enterprises</span>.</h2>
            <p style={{ marginTop:12, fontSize:15, color:'#64748B', maxWidth:620, marginLeft:'auto', marginRight:'auto', textAlign:'center' }}>Across a dozen sectors we ship interfaces that actually move the needle — from first-time founders to publicly-listed brands.</p>
          </div>
        </div>
        <div style={{ display:'grid', gridTemplateColumns:'repeat(auto-fill,minmax(210px,1fr))', gap:14 }}>
          {(data.industries||[]).map((ind,i) => <IndustryCard key={ind} ind={ind} i={i} />)}
        </div>
      </div>
    </section>
  );
}
const INDUSTRY_THEMES = {
  retail:       { accent:'#D97706', tint:'#FEF3C7', soft:'#FFFBEB', grad:'linear-gradient(135deg,#FEF3C7,#FED7AA)' },
  healthcare:   { accent:'#E11D48', tint:'#FFE4E6', soft:'#FFF1F2', grad:'linear-gradient(135deg,#FFE4E6,#FECDD3)' },
  education:    { accent:'#7C3AED', tint:'#EDE9FE', soft:'#F5F3FF', grad:'linear-gradient(135deg,#EDE9FE,#DDD6FE)' },
  travel:       { accent:'#0284C7', tint:'#E0F2FE', soft:'#F0F9FF', grad:'linear-gradient(135deg,#E0F2FE,#BAE6FD)' },
  finance:      { accent:'#059669', tint:'#D1FAE5', soft:'#ECFDF5', grad:'linear-gradient(135deg,#D1FAE5,#A7F3D0)' },
  technology:   { accent:'#2563EB', tint:'#DBEAFE', soft:'#EFF6FF', grad:'linear-gradient(135deg,#DBEAFE,#BFDBFE)' },
  logistics:    { accent:'#EA580C', tint:'#FFEDD5', soft:'#FFF7ED', grad:'linear-gradient(135deg,#FFEDD5,#FED7AA)' },
  hospitality:  { accent:'#DB2777', tint:'#FCE7F3', soft:'#FDF2F8', grad:'linear-gradient(135deg,#FCE7F3,#FBCFE8)' },
  automotive:   { accent:'#334155', tint:'#E2E8F0', soft:'#F8FAFC', grad:'linear-gradient(135deg,#E2E8F0,#CBD5E1)' },
  sports:       { accent:'#CA8A04', tint:'#FEF9C3', soft:'#FEFCE8', grad:'linear-gradient(135deg,#FEF9C3,#FDE68A)' },
  realEstate:   { accent:'#0D9488', tint:'#CCFBF1', soft:'#F0FDFA', grad:'linear-gradient(135deg,#CCFBF1,#99F6E4)' },
  food:         { accent:'#B45309', tint:'#FEF3C7', soft:'#FFFBEB', grad:'linear-gradient(135deg,#FEF3C7,#FDE68A)' },
  industrial:   { accent:'#475569', tint:'#E2E8F0', soft:'#F8FAFC', grad:'linear-gradient(135deg,#E2E8F0,#CBD5E1)' },
  solar:        { accent:'#F59E0B', tint:'#FEF3C7', soft:'#FFFBEB', grad:'linear-gradient(135deg,#FEF3C7,#FDE68A)' },
  entertainment:{ accent:'#9333EA', tint:'#F3E8FF', soft:'#FAF5FF', grad:'linear-gradient(135deg,#F3E8FF,#E9D5FF)' },
  lifestyle:    { accent:'#EC4899', tint:'#FCE7F3', soft:'#FDF2F8', grad:'linear-gradient(135deg,#FCE7F3,#FBCFE8)' },
  brand:        { accent:'#8B5CF6', tint:'#EDE9FE', soft:'#F5F3FF', grad:'linear-gradient(135deg,#EDE9FE,#DDD6FE)' },
  ngo:          { accent:'#E11D48', tint:'#FFE4E6', soft:'#FFF1F2', grad:'linear-gradient(135deg,#FFE4E6,#FECDD3)' },
  professional: { accent:'#1E40AF', tint:'#DBEAFE', soft:'#EFF6FF', grad:'linear-gradient(135deg,#DBEAFE,#BFDBFE)' },
  default:      { accent:'#1E40AF', tint:'#DBEAFE', soft:'#EFF6FF', grad:'linear-gradient(135deg,#DBEAFE,#BFDBFE)' },
};

function industryTheme(name) {
  const n = (name || '').toLowerCase();
  if (n.includes('retail') || n.includes('ecommerce') || n.includes('e-commerce') || n.includes('shop')) return INDUSTRY_THEMES.retail;
  if (n.includes('health') || n.includes('medical') || n.includes('pharma')) return INDUSTRY_THEMES.healthcare;
  if (n.includes('education') || n.includes('school') || n.includes('learn')) return INDUSTRY_THEMES.education;
  if (n.includes('travel') || n.includes('tourism') || n.includes('airline')) return INDUSTRY_THEMES.travel;
  if (n.includes('finance') || n.includes('bank') || n.includes('fintech')) return INDUSTRY_THEMES.finance;
  if (n.includes('tech') || n.includes('software') || n.includes('saas')) return INDUSTRY_THEMES.technology;
  if (n.includes('logistic') || n.includes('shipping') || n.includes('delivery')) return INDUSTRY_THEMES.logistics;
  if (n.includes('hospitality') || n.includes('hotel') || n.includes('resort')) return INDUSTRY_THEMES.hospitality;
  if (n.includes('auto') || n.includes('motor') || n.includes('vehicle')) return INDUSTRY_THEMES.automotive;
  if (n.includes('sport') || n.includes('fitness') || n.includes('gym')) return INDUSTRY_THEMES.sports;
  if (n.includes('real estate') || n.includes('property')) return INDUSTRY_THEMES.realEstate;
  if (n.includes('food') || n.includes('beverage') || n.includes('restaurant') || n.includes('cafe')) return INDUSTRY_THEMES.food;
  if (n.includes('industrial') || n.includes('manufactur') || n.includes('factory')) return INDUSTRY_THEMES.industrial;
  if (n.includes('solar') || n.includes('energy') || n.includes('power')) return INDUSTRY_THEMES.solar;
  if (n.includes('entertainment') || n.includes('media') || n.includes('film')) return INDUSTRY_THEMES.entertainment;
  if (n.includes('lifestyle') || n.includes('beauty')) return INDUSTRY_THEMES.lifestyle;
  if (n.includes('brand') || n.includes('design') || n.includes('creative')) return INDUSTRY_THEMES.brand;
  if (n.includes('ngo') || n.includes('non-profit') || n.includes('nonprofit') || n.includes('charity')) return INDUSTRY_THEMES.ngo;
  if (n.includes('professional') || n.includes('consulting') || n.includes('legal')) return INDUSTRY_THEMES.professional;
  return INDUSTRY_THEMES.default;
}

function industryIcon(name) {
  const n = (name || '').toLowerCase();
  if (n.includes('retail') || n.includes('ecommerce') || n.includes('e-commerce') || n.includes('shop')) return ShoppingBag;
  if (n.includes('health') || n.includes('medical') || n.includes('pharma')) return HeartPulse;
  if (n.includes('education') || n.includes('school') || n.includes('learn')) return GraduationCap;
  if (n.includes('travel') || n.includes('tourism') || n.includes('airline')) return Plane;
  if (n.includes('finance') || n.includes('bank') || n.includes('fintech')) return Landmark;
  if (n.includes('tech') || n.includes('software') || n.includes('saas') || n.includes('it ')) return Cpu;
  if (n.includes('logistic') || n.includes('shipping') || n.includes('delivery')) return Truck;
  if (n.includes('hospitality') || n.includes('hotel') || n.includes('resort')) return Hotel;
  if (n.includes('auto') || n.includes('motor') || n.includes('vehicle')) return Car;
  if (n.includes('sport') || n.includes('fitness') || n.includes('gym')) return Trophy;
  if (n.includes('real estate') || n.includes('property') || n.includes('housing')) return Home;
  if (n.includes('food') || n.includes('beverage') || n.includes('restaurant') || n.includes('cafe')) return UtensilsCrossed;
  if (n.includes('industrial') || n.includes('manufactur') || n.includes('factory')) return Factory;
  if (n.includes('solar') || n.includes('energy') || n.includes('power')) return Sun;
  if (n.includes('entertainment') || n.includes('media') || n.includes('film')) return Film;
  if (n.includes('lifestyle') || n.includes('beauty')) return Sparkles;
  if (n.includes('brand') || n.includes('design') || n.includes('creative')) return Palette;
  if (n.includes('ngo') || n.includes('non-profit') || n.includes('nonprofit') || n.includes('charity')) return HeartPulse;
  if (n.includes('professional') || n.includes('consulting') || n.includes('legal')) return Briefcase;
  return Briefcase;
}

function IndustryCard({ ind, i }) {
  const [ref, vis] = useReveal();
  const Icon = industryIcon(ind);
  const t = industryTheme(ind);
  const num = String(i+1).padStart(2,'0');
  return (
    <div ref={ref} className={`ind-card reveal ${vis?'in':''}`}
      style={{ transitionDelay:`${i*40}ms`, background:'#fff', border:`1px solid ${t.tint}`, boxShadow:`0 1px 0 ${t.soft}` }}
      onMouseOver={e => { e.currentTarget.style.borderColor = t.accent; e.currentTarget.style.boxShadow = `0 18px 44px -14px ${t.accent}55`; }}
      onMouseOut={e => { e.currentTarget.style.borderColor = t.tint; e.currentTarget.style.boxShadow = `0 1px 0 ${t.soft}`; }}>
      <div className="ind-bg" style={{ background:t.grad }} />
      <div className="ind-corner" style={{ background:t.accent }} />
      <span className="ind-watermark" style={{ color:t.accent }}>{num}</span>
      <svg className="ind-dots" viewBox="0 0 52 22" aria-hidden="true">
        {[0,1,2,3].map(r => [0,1,2,3,4,5,6,7,8].map(c => (
          <circle key={`${r}-${c}`} cx={2+c*6} cy={2+r*6} r="1" fill={t.accent} />
        )))}
      </svg>
      <div style={{ position:'relative', display:'flex', alignItems:'center', justifyContent:'space-between', marginBottom:16, zIndex:1 }}>
        <div className="ind-badge" style={{ background:t.soft, border:`1.5px solid ${t.tint}`, color:t.accent }}>
          <span className="ind-ring" />
          <Icon size={20} color={t.accent} strokeWidth={2.2} />
        </div>
        <span className="mono" style={{ fontSize:11, fontWeight:600, letterSpacing:'0.14em', color:t.accent, opacity:.7 }}>{num}</span>
      </div>
      <div className="display" style={{ position:'relative', fontSize:16, color:'#0F172A', lineHeight:1.3, fontWeight:600, zIndex:1 }}>{ind}</div>
      <div className="ind-cta" style={{ color:t.accent, position:'relative', zIndex:1 }}>
        <span className="cta-line" />
        <span>Explore</span>
        <ArrowUpRight size={13} strokeWidth={2.5} />
      </div>
    </div>
  );
}

// ─── Freelancing Platforms ────────────────────────────────────────────────────
function Stars({ value = 0, size = 22 }) {
  const full = Math.floor(value);
  const half = value - full >= 0.5;
  return (
    <div style={{ display:'inline-flex', gap:3 }}>
      {[0,1,2,3,4].map(i => {
        const isFull = i < full;
        const isHalf = i === full && half;
        const fill = isFull ? '#FBBF24' : isHalf ? 'url(#half-grad)' : 'rgba(255,255,255,.2)';
        return (
          <span key={i} className="fl-star" style={{ animationDelay: `${i*0.1}s` }}>
            <svg width={size} height={size} viewBox="0 0 24 24" fill={fill} stroke="#FBBF24" strokeWidth="1" strokeLinejoin="round">
              <defs>
                <linearGradient id="half-grad" x1="0" x2="1" y1="0" y2="0">
                  <stop offset="50%" stopColor="#FBBF24" />
                  <stop offset="50%" stopColor="rgba(255,255,255,.2)" />
                </linearGradient>
              </defs>
              <path d="M12 2l3.09 6.26L22 9.27l-5 4.87 1.18 6.88L12 17.77l-6.18 3.25L7 14.14 2 9.27l6.91-1.01L12 2z"/>
            </svg>
          </span>
        );
      })}
    </div>
  );
}

function PlatformCard({ platform }) {
  const p = platform;
  return (
    <div className="fl-card" style={{ background:p.bg }}>
      <div className="fl-shine" />

      {/* Header */}
      <div style={{ position:'relative', zIndex:1, display:'flex', alignItems:'center', gap:14, marginBottom:18, paddingBottom:18, borderBottom:'1px solid rgba(255,255,255,.1)' }}>
        <div style={{ width:54, height:54, borderRadius:14, background:'#fff', display:'flex', alignItems:'center', justifyContent:'center', flexShrink:0, boxShadow:'0 8px 20px -6px rgba(0,0,0,.35)' }}>
          <FadeImg src={p.logo} alt={p.name} width={32} height={32} style={{ display:'block' }} />
        </div>
        <div style={{ flex:1, minWidth:0 }}>
          <h3 className="display" style={{ fontSize:22, fontWeight:600, color:'#fff', margin:0, lineHeight:1.1 }}>{p.name}</h3>
          <a href={p.url} target="_blank" rel="noopener noreferrer" className="mono" style={{ fontSize:12, color:p.accentLight, textDecoration:'none', display:'inline-flex', alignItems:'center', gap:5, marginTop:4 }}>
            {p.handle} <ExternalLink size={11} />
          </a>
        </div>
        <span style={{ display:'inline-flex', alignItems:'center', gap:5, background:`${p.accent}22`, border:`1px solid ${p.accent}55`, borderRadius:99, padding:'4px 10px', fontSize:10, color:p.accentLight, fontFamily:'Geist Mono,monospace', textTransform:'uppercase', letterSpacing:'0.1em', flexShrink:0 }}>
          <BadgeCheck size={11} /> Verified
        </span>
      </div>

      {/* Badges */}
      <div style={{ position:'relative', zIndex:1, display:'flex', gap:6, flexWrap:'wrap', marginBottom:20 }}>
        {p.badges.map(b => (
          <span key={b.label} className="fl-badge" style={{ background:b.bg, color:'#fff' }}>
            <b.Icon size={11} /> {b.label}
          </span>
        ))}
      </div>

      {/* Stats — compact horizontal rows */}
      <div className="fl-row-list" style={{ position:'relative', zIndex:1, marginBottom:22 }}>
        {p.stats.map((s, i) => {
          const Ic = s.icon;
          return (
            <div key={i} className="fl-row">
              <span className="fl-row-icon" style={{ background:`${p.accent}22`, border:`1px solid ${p.accent}40` }}>
                <Ic size={14} color={p.accent} strokeWidth={2.2} />
              </span>
              <span className="fl-row-label" style={{ color:p.accentLight }}>{s.label}</span>
              <span className="fl-row-value">
                {s.value}
                {s.suffix && <span className="mono" style={{ fontSize:11, color:p.accentLight, fontWeight:400 }}>{s.suffix}</span>}
              </span>
              <span className="fl-row-side">{s.side}</span>
            </div>
          );
        })}
      </div>

      {/* Footer CTA */}
      <div style={{ position:'relative', zIndex:1, display:'flex', alignItems:'center', justifyContent:'space-between', gap:12, paddingTop:16, borderTop:'1px solid rgba(255,255,255,.1)' }}>
        <div style={{ fontSize:12, color:p.accentLight, lineHeight:1.5, flex:1 }}>{p.tagline}</div>
        <a href={p.url} target="_blank" rel="noopener noreferrer" className="fl-cta" style={{ background:p.ctaGrad, boxShadow:`0 10px 26px -8px ${p.accent}88`, fontSize:11, padding:'11px 20px', flexShrink:0 }}>
          View <ArrowUpRight size={14} strokeWidth={2.5} />
        </a>
      </div>
    </div>
  );
}

function PlatformsSection() {
  const [ref, vis] = useReveal();
  const freelancer = {
    name: 'Freelancer',
    handle: '@royprosenjit1015',
    url: 'https://www.freelancer.com/u/royprosenjit1015',
    logo: 'https://cdn.simpleicons.org/freelancer/29B2FE',
    accent: '#29B2FE',
    accentLight: '#93C5FD',
    bg: 'linear-gradient(135deg,#0B1A38 0%,#102E63 50%,#0B1A38 100%)',
    ctaGrad: 'linear-gradient(135deg,#29B2FE,#0284C7)',
    badges: [
      { label: 'Level 4 Monthly', Icon: Trophy, bg: 'linear-gradient(135deg,#EAB308,#CA8A04)' },
      { label: 'Verified', Icon: BadgeCheck, bg: 'linear-gradient(135deg,#22C55E,#16A34A)' },
      { label: 'Preferred Freelancer', Icon: Star, bg: 'linear-gradient(135deg,#DB2777,#BE185D)' },
    ],
    stats: [
      { label:'Rating',    value:'4.9',   suffix:'/ 5',  icon:Star,        side:<Stars value={4.9} size={12} /> },
      { label:'Reviews',   value:'1,092',                icon:Users,       side:<span className="mono" style={{ fontSize:10, color:'#22C55E', display:'inline-flex', alignItems:'center', gap:4 }}><TrendingUp size={10} /> verified</span> },
      { label:'Earnings',  value:'8.7',   suffix:'/ 10', icon:TrendingUp,  side:<span style={{ width:64, height:4, background:'rgba(255,255,255,.15)', borderRadius:99, overflow:'hidden', display:'inline-block' }}><span style={{ display:'block', height:'100%', width:'87%', background:'linear-gradient(90deg,#29B2FE,#0284C7)' }} /></span> },
      { label:'On-Budget', value:'100%',                 icon:CheckCircle2,side:<span className="mono" style={{ fontSize:10, color:'#22C55E', display:'inline-flex', alignItems:'center', gap:4 }}><CheckCircle2 size={10} /> paid</span> },
    ],
    tagline: 'Top 1% on Freelancer.com — a decade of consistent 5-star delivery.',
  };
  const upwork = {
    name: 'Upwork',
    handle: '~014f2960cc154ca130',
    url: 'https://www.upwork.com/freelancers/~014f2960cc154ca130',
    logo: 'https://cdn.simpleicons.org/upwork/14A800',
    accent: '#14A800',
    accentLight: '#86EFAC',
    bg: 'linear-gradient(135deg,#052E16 0%,#14532D 50%,#052E16 100%)',
    ctaGrad: 'linear-gradient(135deg,#14A800,#0C6B00)',
    badges: [
      { label: 'Top Rated', Icon: Star, bg: 'linear-gradient(135deg,#14A800,#0C6B00)' },
      { label: 'Identity Verified', Icon: BadgeCheck, bg: 'linear-gradient(135deg,#22C55E,#16A34A)' },
      { label: 'Expert Vetted', Icon: Shield, bg: 'linear-gradient(135deg,#7C3AED,#5B21B6)' },
    ],
    stats: [
      { label:'Jobs Done',    value:'113+',                icon:BadgeCheck,  side:<span className="mono" style={{ fontSize:10, color:'#86EFAC', display:'inline-flex', alignItems:'center', gap:4 }}><TrendingUp size={10} /> completed</span> },
      { label:'Completion',   value:'100%',                icon:CheckCircle2,side:<span className="mono" style={{ fontSize:10, color:'#86EFAC', display:'inline-flex', alignItems:'center', gap:4 }}><CheckCircle2 size={10} /> success</span> },
      { label:'On-Time',      value:'98%',                 icon:Clock,       side:<span style={{ width:64, height:4, background:'rgba(255,255,255,.15)', borderRadius:99, overflow:'hidden', display:'inline-block' }}><span style={{ display:'block', height:'100%', width:'98%', background:'linear-gradient(90deg,#14A800,#22C55E)' }} /></span> },
      { label:'Client Score', value:'5.0',   suffix:'/ 5', icon:Star,        side:<Stars value={5} size={12} /> },
    ],
    tagline: 'Consistently Top-Rated on Upwork — perfect completion, on-time delivery.',
  };
  return (
    <section id="platforms" style={{ padding:'80px 5%', background:'linear-gradient(180deg,#F8FAFF 0%,#EFF6FF 100%)', borderTop:'1px solid #DBEAFE' }}>
      <div style={{ maxWidth:1200, margin:'0 auto' }}>
        <div ref={ref} className={`reveal ${vis?'in':''}`} style={{ textAlign:'center', marginBottom:36 }}>
          <div style={{ display:'inline-flex', alignItems:'center', gap:8, padding:'6px 14px', background:'#fff', border:'1px solid #DBEAFE', borderRadius:99, marginBottom:16 }}>
            <BadgeCheck size={13} color="#1E40AF" />
            <span className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.15em', color:'#1E40AF', fontWeight:600 }}>Verified Freelancing Credentials</span>
          </div>
          <h2 className="display" style={{ fontSize:'clamp(1.8rem,4vw,3rem)', color:'#0F172A', lineHeight:1.12, margin:0 }}>
            Our <span className="display-it" style={{ background:'linear-gradient(90deg,#29B2FE,#14A800)', WebkitBackgroundClip:'text', WebkitTextFillColor:'transparent', backgroundClip:'text' }}>public track record</span>.
          </h2>
          <p style={{ fontSize:15, color:'#64748B', marginTop:12, maxWidth:620, margin:'12px auto 0' }}>Two of the world's largest freelancing platforms — both independently verify our ratings and delivery history.</p>
        </div>
        <div className={`reveal ${vis?'in':''} delay-200`} style={{ display:'grid', gridTemplateColumns:'repeat(auto-fit,minmax(min(100%,460px),1fr))', gap:20 }}>
          <PlatformCard platform={freelancer} />
          <PlatformCard platform={upwork} />
        </div>
      </div>
    </section>
  );
}

// ─── Contact ──────────────────────────────────────────────────────────────────
function NetBackground() {
  const canvasRef = useRef(null);
  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    const ctx = canvas.getContext('2d');
    const dpr = window.devicePixelRatio || 1;
    let width = 0, height = 0, raf = 0;
    const mouse = { x: -9999, y: -9999 };

    const resize = () => {
      const rect = canvas.getBoundingClientRect();
      width = rect.width; height = rect.height;
      canvas.width = Math.max(1, Math.floor(width * dpr));
      canvas.height = Math.max(1, Math.floor(height * dpr));
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    };
    resize();

    const count = Math.max(36, Math.min(110, Math.floor((width * height) / 16000)));
    const parts = Array.from({ length: count }, () => ({
      x: Math.random() * width,
      y: Math.random() * height,
      vx: (Math.random() - 0.5) * 0.35,
      vy: (Math.random() - 0.5) * 0.35,
      r: Math.random() * 1.4 + 0.7,
    }));

    const onMove = (e) => {
      const rect = canvas.getBoundingClientRect();
      if (e.clientX < rect.left || e.clientX > rect.right || e.clientY < rect.top || e.clientY > rect.bottom) {
        mouse.x = -9999; mouse.y = -9999;
      } else {
        mouse.x = e.clientX - rect.left;
        mouse.y = e.clientY - rect.top;
      }
    };
    const onLeave = () => { mouse.x = -9999; mouse.y = -9999; };
    window.addEventListener('mousemove', onMove);
    window.addEventListener('mouseout', onLeave);
    window.addEventListener('resize', resize);

    const linkDist = 130;
    const mouseDist = 190;
    const draw = () => {
      ctx.clearRect(0, 0, width, height);
      for (const p of parts) {
        p.x += p.vx; p.y += p.vy;
        if (p.x < 0 || p.x > width) p.vx *= -1;
        if (p.y < 0 || p.y > height) p.vy *= -1;
      }
      for (let i = 0; i < parts.length; i++) {
        for (let j = i + 1; j < parts.length; j++) {
          const dx = parts[i].x - parts[j].x, dy = parts[i].y - parts[j].y;
          const d2 = dx*dx + dy*dy;
          if (d2 < linkDist * linkDist) {
            const a = (1 - Math.sqrt(d2) / linkDist) * 0.32;
            ctx.strokeStyle = `rgba(96,165,250,${a})`;
            ctx.lineWidth = 1;
            ctx.beginPath();
            ctx.moveTo(parts[i].x, parts[i].y);
            ctx.lineTo(parts[j].x, parts[j].y);
            ctx.stroke();
          }
        }
      }
      for (const p of parts) {
        const dx = p.x - mouse.x, dy = p.y - mouse.y;
        const d2 = dx*dx + dy*dy;
        if (d2 < mouseDist * mouseDist) {
          const d = Math.sqrt(d2);
          const a = (1 - d / mouseDist) * 0.75;
          ctx.strokeStyle = `rgba(147,197,253,${a})`;
          ctx.lineWidth = 1;
          ctx.beginPath();
          ctx.moveTo(p.x, p.y);
          ctx.lineTo(mouse.x, mouse.y);
          ctx.stroke();
          const pull = (1 - d / mouseDist) * 0.04;
          p.x += (mouse.x - p.x) * pull * 0.02;
          p.y += (mouse.y - p.y) * pull * 0.02;
        }
      }
      ctx.fillStyle = 'rgba(147,197,253,0.75)';
      for (const p of parts) {
        ctx.beginPath();
        ctx.arc(p.x, p.y, p.r, 0, Math.PI * 2);
        ctx.fill();
      }
      raf = requestAnimationFrame(draw);
    };
    draw();

    return () => {
      cancelAnimationFrame(raf);
      window.removeEventListener('mousemove', onMove);
      window.removeEventListener('mouseout', onLeave);
      window.removeEventListener('resize', resize);
    };
  }, []);

  return <canvas ref={canvasRef} style={{ position:'absolute', inset:0, width:'100%', height:'100%', pointerEvents:'none', zIndex:0 }} />;
}

function ContactSection({ data }) {
  const [ref, vis] = useReveal();
  const c = data.contact || {};
  return (
    <section id="contact" style={{ padding:'80px 5% 60px', background:'#0F1D3E', color:'#fff', overflow:'hidden', position:'relative', textAlign:'left' }}>
      <div className="blob anim-float" style={{ width:500, height:500, background:'#1E40AF', top:-150, right:-100, opacity:.15 }} />
      <NetBackground />
      <div ref={ref} className={`reveal ${vis ? 'in' : ''}`} style={{ maxWidth:1200, margin:'0 auto', position:'relative', zIndex:1, textAlign:'left' }}>
        <div style={{ display:'grid', gridTemplateColumns:'repeat(auto-fit,minmax(320px,1fr))', gap:40, alignItems:'center', marginBottom:48 }}>
          <div style={{ textAlign:'left' }}>
            <div className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.15em', color:'#60A5FA', marginBottom:20 }}>§ Let's Work Together</div>
            <h2 className="display" style={{ fontSize:'clamp(2.5rem,8vw,6rem)', lineHeight:1.05, marginBottom:18, color:'#fff', textAlign:'left' }}>
              Have a <span className="display-it" style={{ color:'#60A5FA' }}>project</span><br />in mind?
            </h2>
            <p style={{ color:'#93C5FD', maxWidth:500, lineHeight:1.7, textAlign:'left', fontSize:15 }}>
              Call, WhatsApp, or email — our senior team is ready to discuss your requirements and send a free detailed quote.
            </p>
            <div style={{ marginTop:24, display:'flex', flexWrap:'wrap', gap:12, alignItems:'center' }}>
              <a href={`https://wa.me/${(c.phones?.[0]||'').replace(/\D/g,'')}`} target="_blank" rel="noopener noreferrer" className="contact-cta contact-cta-primary">
                <MessageCircle size={16} />
                <span>Start a Conversation</span>
                <ArrowUpRight size={15} />
              </a>
              <a href={`mailto:${c.email}`} className="contact-cta contact-cta-ghost">
                <Mail size={16} />
                <span>Email Us</span>
              </a>
            </div>
          </div>
          <div style={{ width:'100%', height:'clamp(280px, 42vw, 460px)' }}>
            <model-viewer
              src="/low_poly_man_working_at_a_table_with_a_laptop.glb"
              alt="Low poly man working at a table with a laptop"
              auto-rotate
              camera-controls
              disable-zoom
              interaction-prompt="none"
              shadow-intensity="1"
              exposure="1"
              style={{ width:'100%', height:'100%', background:'transparent', '--poster-color':'transparent' }}
            />
          </div>
        </div>
        
        {/* Contact Info Cards */}
        <div style={{ display:'grid', gridTemplateColumns:'repeat(auto-fit,minmax(260px,1fr))', gap:20, paddingTop:36, borderTop:'1px solid rgba(255,255,255,.12)' }}>
          <CBlock icon={Mail} label="Email">
            <a
              href={`mailto:${c.email}`}
              style={{ color:'#fff', fontSize:15, fontWeight:600, textDecoration:'none', wordBreak:'break-all', display:'inline-block', transition:'color .15s' }}
              onMouseEnter={e => e.currentTarget.style.color = '#60A5FA'}
              onMouseLeave={e => e.currentTarget.style.color = '#fff'}
            >
              {c.email}
            </a>
          </CBlock>
          <CBlock icon={Phone} label="Call / WhatsApp">
            {(c.phones||[]).map(p => (
              <a
                key={p}
                href={`tel:${p.replace(/\s/g,'')}`}
                style={{ display:'block', color:'#fff', fontSize:15, fontWeight:600, textDecoration:'none', marginBottom:6, transition:'color .15s' }}
                onMouseEnter={e => e.currentTarget.style.color = '#60A5FA'}
                onMouseLeave={e => e.currentTarget.style.color = '#fff'}
              >
                {p}
              </a>
            ))}
          </CBlock>
          <CBlock icon={MapPin} label="Studio">
            <div style={{ color:'#E2E8F0', fontSize:13.5, lineHeight:1.65, whiteSpace:'pre-line', textAlign:'left' }}>
              {c.address}
            </div>
          </CBlock>
        </div>

        <div style={{ marginTop:44, paddingTop:24, borderTop:'1px solid rgba(255,255,255,.1)', display:'flex', flexWrap:'wrap', justifyContent:'space-between', alignItems:'center', gap:12, textAlign:'left' }}>
          <div className="mono" style={{ fontSize:11, color:'#94A3B8', textTransform:'uppercase', letterSpacing:'0.08em' }}>
            © {new Date().getFullYear()} Techpenta e-Solutions Pvt. Ltd. All rights reserved.
          </div>
          <div style={{ display:'flex', gap:18 }}>
            <a href="#hero" className="mono" style={{ fontSize:11, color:'#60A5FA', textDecoration:'none', textTransform:'uppercase', letterSpacing:'0.08em', display:'inline-flex', alignItems:'center', gap:4 }}>
              <span>Back to Top</span> ↑
            </a>
          </div>
        </div>
      </div>
    </section>
  );
}
function CBlock({ icon: Icon, label, children }) {
  return (
    <div style={{
      background:'rgba(255,255,255,.05)',
      border:'1px solid rgba(255,255,255,.1)',
      borderRadius:16,
      padding:'22px 24px',
      textAlign:'left',
      boxShadow:'0 8px 24px rgba(0,0,0,.2)',
      display:'flex',
      flexDirection:'column',
      justifyContent:'flex-start'
    }}>
      <div style={{ display:'flex', alignItems:'center', gap:10, marginBottom:12 }}>
        <div style={{ width:32, height:32, borderRadius:8, background:'rgba(96,165,250,.18)', color:'#60A5FA', display:'flex', alignItems:'center', justifyContent:'center', flexShrink:0 }}>
          <Icon size={16} />
        </div>
        <span className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.12em', color:'#93C5FD', fontWeight:700 }}>
          {label}
        </span>
      </div>
      <div style={{ textAlign:'left', width:'100%' }}>
        {children}
      </div>
    </div>
  );
}

// ─── Quote Wizard ─────────────────────────────────────────────────────────────
function QuoteWizard({ open, onClose, data, initialProject }) {
  const [step, setStep] = useState(0);
  const [answers, setAnswers] = useState({});
  const [submitted, setSubmitted] = useState(false);
  const [errors, setErrors] = useState({});
  const [sending, setSending] = useState(false);
  const [sendError, setSendError] = useState('');

  useEffect(() => {
    document.body.style.overflow = open ? 'hidden' : '';
    return () => { document.body.style.overflow = ''; };
  }, [open]);

  useEffect(() => {
    if (!open) {
      const t = setTimeout(() => { setStep(0); setAnswers({}); setSubmitted(false); setErrors({}); }, 250);
      return () => clearTimeout(t);
    }
  }, [open]);

    useEffect(() => {
    if (open && initialProject) {
      const isApp = initialProject.categories?.includes('Mobile Apps') || initialProject.type === 'app';
      const isLogo = initialProject.categories?.includes('Brand & Logo') || initialProject.type === 'logo';
      const sType = isApp ? 'app' : isLogo ? 'logo' : 'website';
      setAnswers(prev => ({
        ...prev,
        service: sType,
        industry: initialProject.industry || initialProject.siteType || '',
        description: `Interested in a solution similar to ${initialProject.title} (${initialProject.displayType || initialProject.siteType || 'Project'}).`
      }));
    }
  }, [open, initialProject]);

  if (!open) return null;

  const set = (k, v) => setAnswers(a => ({ ...a, [k]: v }));

  const SERVICES = [
    { id:'website', label:'Website', desc:'Marketing site, e-commerce, web app', Icon: Globe },
    { id:'app',     label:'Mobile App', desc:'iOS, Android or cross-platform', Icon: Smartphone },
    { id:'logo',    label:'Logo & Branding', desc:'Identity, packaging, guidelines', Icon: Palette },
    { id:'other',   label:'Other', desc:'SEO, marketing, custom work', Icon: Sparkles },
  ];

  const INDUSTRIES = [
    { id:'Retail & eCommerce', Icon: ShoppingBag },
    { id:'Healthcare',         Icon: HeartPulse },
    { id:'Education',          Icon: GraduationCap },
    { id:'Travel',             Icon: Plane },
    { id:'Finance',            Icon: Landmark },
    { id:'Technology',         Icon: Cpu },
    { id:'Logistics',          Icon: Truck },
    { id:'Hospitality',        Icon: Hotel },
    { id:'Real Estate',        Icon: Home },
    { id:'Food & Beverage',    Icon: UtensilsCrossed },
    { id:'Automotive',         Icon: Car },
    { id:'Other',              Icon: Briefcase },
  ];

  const WEB_PLATFORMS = [
    { id:'WordPress',           desc:'Fast to launch, easy to manage', Icon: Layers },
    { id:'Next.js + Laravel',   desc:'Full-stack with custom backend', Icon: Code },
    { id:'Next.js only',        desc:'Modern frontend / headless',     Icon: Zap },
    { id:'Shopify',             desc:'E-commerce, hosted',             Icon: ShoppingBag },
    { id:'Other / Not sure',    desc:'We\'ll recommend a stack',       Icon: Sparkles },
  ];

  const WP_EDITORS = [
    { id:'Elementor',       desc:'Drag-and-drop, fastest', Icon: Layers },
    { id:'Visual Composer', desc:'Page builder',           Icon: Layers },
    { id:'Custom theme',    desc:'Hand-coded, no builder', Icon: Code },
    { id:'Not sure',        desc:'You decide for me',      Icon: Sparkles },
  ];

  const APP_PLATFORMS = [
    { id:'iOS only',         Icon: Smartphone },
    { id:'Android only',     Icon: Smartphone },
    { id:'Cross-platform',   Icon: Layers },
    { id:'Not sure',         Icon: Sparkles },
  ];

  const LOGO_KINDS = [
    { id:'Brand identity (full)', Icon: Palette },
    { id:'Just the logo mark',    Icon: Sparkles },
    { id:'Rebrand / refresh',     Icon: Rocket },
    { id:'Not sure',              Icon: Briefcase },
  ];

  const flow = (() => {
    const s = answers.service;
    if (!s) return ['service'];
    if (s === 'website') return ['service', 'industry', 'platform', ...(answers.platform === 'WordPress' ? ['wpEditor'] : []), 'details'];
    if (s === 'app')     return ['service', 'appPlatform', 'details'];
    if (s === 'logo')    return ['service', 'logoKind', 'details'];
    return ['service', 'details'];
  })();
  const currentKey = flow[step];
  const total = flow.length;
  const progress = ((step + 1) / total) * 100;

  const next = () => setStep(s => Math.min(s + 1, flow.length - 1));
  const back = () => setStep(s => Math.max(s - 1, 0));

  const submit = async () => {
    const e = {};
    if (!answers.name?.trim()) e.name = 'Required';
    if (!answers.email?.trim()) e.email = 'Required';
    else if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(answers.email.trim())) e.email = 'Invalid email';
    setErrors(e);
    if (Object.keys(e).length) return;
    setSending(true); setSendError('');
    try {
      const res = await fetch('/api/quote', {
        method:'POST',
        headers:{'Content-Type':'application/json'},
        body: JSON.stringify(answers),
      });
      const j = await res.json().catch(() => ({}));
      if (!res.ok || j.error) throw new Error(j.error || 'Failed to send');
      setSubmitted(true);
    } catch (err) {
      setSendError(err.message || 'Could not send request. Please try again or email us directly.');
    } finally {
      setSending(false);
    }
  };

  const Card = ({ active, onClick, children, style }) => (
    <button type="button" onClick={onClick}
      style={{ textAlign:'left', cursor:'pointer', background: active ? '#EFF6FF' : '#fff', border: active ? '2px solid #2563EB' : '2px solid #E2E8F0', borderRadius:14, padding:16, transition:'all .15s', boxShadow: active ? '0 6px 20px rgba(37,99,235,.18)' : '0 1px 2px rgba(15,23,42,.04)', ...style }}
      onMouseEnter={e => { if (!active) { e.currentTarget.style.borderColor = '#93C5FD'; e.currentTarget.style.transform = 'translateY(-1px)'; } }}
      onMouseLeave={e => { if (!active) { e.currentTarget.style.borderColor = '#E2E8F0'; e.currentTarget.style.transform = 'none'; } }}>
      {children}
    </button>
  );

  const IconCard = ({ Icon, label, desc, active, onClick }) => (
    <Card active={active} onClick={onClick}>
      <div style={{ display:'flex', alignItems:'flex-start', gap:12 }}>
        <div style={{ width:42, height:42, borderRadius:10, background: active ? '#2563EB' : '#EFF6FF', color: active ? '#fff' : '#2563EB', display:'flex', alignItems:'center', justifyContent:'center', flexShrink:0, transition:'all .15s' }}>
          <Icon size={20} />
        </div>
        <div style={{ flex:1, minWidth:0 }}>
          <div style={{ fontWeight:700, fontSize:14, color:'#0F172A', marginBottom: desc ? 3 : 0 }}>{label}</div>
          {desc && <div style={{ fontSize:12, color:'#64748B', lineHeight:1.4 }}>{desc}</div>}
        </div>
      </div>
    </Card>
  );

  const CompactCard = ({ Icon, label, active, onClick }) => (
    <Card active={active} onClick={onClick} style={{ padding:14 }}>
      <div style={{ display:'flex', flexDirection:'column', alignItems:'center', justifyContent:'center', gap:8, minHeight:78 }}>
        <Icon size={22} color={active ? '#2563EB' : '#64748B'} />
        <div style={{ fontWeight:600, fontSize:12.5, color:'#0F172A', textAlign:'center', lineHeight:1.25 }}>{label}</div>
      </div>
    </Card>
  );

  const stepTitle = {
    service:     ['What can we build for you?', 'Pick a starting point — you can change anything later.'],
    industry:    ['Which industry?', 'Helps us match you with the right team.'],
    platform:    ['Preferred platform?', 'Not sure? Pick "Other / Not sure" and we\'ll recommend.'],
    wpEditor:    ['How should we build it in WordPress?', 'Editors trade off speed of changes vs. performance.'],
    appPlatform: ['Target platform?', ''],
    logoKind:    ['What kind of logo work?', ''],
    details:     ['A few quick details', 'We\'ll reply within 24 hours.'],
  }[currentKey] || ['', ''];

  const canAdvance = (() => {
    if (currentKey === 'service')     return !!answers.service;
    if (currentKey === 'industry')    return !!answers.industry;
    if (currentKey === 'platform')    return !!answers.platform;
    if (currentKey === 'wpEditor')    return !!answers.wpEditor;
    if (currentKey === 'appPlatform') return !!answers.appPlatform;
    if (currentKey === 'logoKind')    return !!answers.logoKind;
    return true;
  })();

  return (
    <div style={{ position:'fixed', inset:0, zIndex:60, background:'rgba(15,23,42,.78)', backdropFilter:'blur(6px)', display:'flex', alignItems:'flex-start', justifyContent:'center', padding:16, overflowY:'auto' }} onClick={onClose}>
      <div className="anim-fadeUp" style={{ width:'100%', maxWidth:640, background:'#fff', borderRadius:20, overflow:'hidden', boxShadow:'0 32px 80px rgba(30,64,175,.32)', marginTop:'min(6vh, 48px)', marginBottom:24 }} onClick={e => e.stopPropagation()}>

        {/* Header */}
        <div style={{ padding:'18px 22px', borderBottom:'1px solid #E2E8F0', display:'flex', alignItems:'center', gap:12, background:'#F8FAFC' }}>
          <div style={{ width:36, height:36, borderRadius:10, background:'#2563EB', color:'#fff', display:'flex', alignItems:'center', justifyContent:'center', flexShrink:0 }}>
            <Sparkles size={18} />
          </div>
          <div style={{ flex:1, minWidth:0 }}>
            <div style={{ fontWeight:800, fontSize:15, color:'#0F172A' }}>Get a Free Quote</div>
            <div style={{ fontSize:11.5, color:'#64748B', fontFamily:'Geist Mono,monospace', textTransform:'uppercase', letterSpacing:'0.08em' }}>{submitted ? 'Sent' : `Step ${Math.min(step + 1, total)} of ${total}`}</div>
          </div>
          <button onClick={onClose} aria-label="Close"
            style={{ width:34, height:34, borderRadius:'50%', background:'#fff', border:'1.5px solid #E2E8F0', cursor:'pointer', color:'#475569', display:'flex', alignItems:'center', justifyContent:'center', flexShrink:0, transition:'all .15s' }}
            onMouseEnter={e=>{ e.currentTarget.style.background='#EF4444'; e.currentTarget.style.borderColor='#EF4444'; e.currentTarget.style.color='#fff'; }}
            onMouseLeave={e=>{ e.currentTarget.style.background='#fff'; e.currentTarget.style.borderColor='#E2E8F0'; e.currentTarget.style.color='#475569'; }}>
            <X size={16} strokeWidth={2.5} />
          </button>
        </div>

        {/* Progress bar */}
        {!submitted && (
          <div style={{ height:4, background:'#E2E8F0' }}>
            <div style={{ height:'100%', width:`${progress}%`, background:'linear-gradient(90deg,#3B82F6,#2563EB)', transition:'width .35s ease' }} />
          </div>
        )}

        {/* Body */}
        <div style={{ padding:'22px 22px 8px' }}>
          {submitted ? (
            <div style={{ textAlign:'center', padding:'28px 8px 32px' }}>
              <div style={{ width:72, height:72, borderRadius:'50%', background:'#DCFCE7', color:'#16A34A', display:'flex', alignItems:'center', justifyContent:'center', margin:'0 auto 18px' }}>
                <CheckCircle2 size={40} strokeWidth={2.4} />
              </div>
              <h3 style={{ fontSize:22, fontWeight:800, color:'#0F172A', marginBottom:8 }}>Thanks, {answers.name?.split(' ')[0] || 'there'}!</h3>
              <p style={{ fontSize:14.5, color:'#475569', lineHeight:1.6, maxWidth:420, margin:'0 auto 22px' }}>
                Your request is in. We'll review the details and contact you at <strong style={{ color:'#0F172A' }}>{answers.email}</strong> within <strong style={{ color:'#0F172A' }}>24 hours</strong>.
              </p>
              <div style={{ display:'inline-flex', alignItems:'center', gap:8, padding:'8px 14px', borderRadius:99, background:'#EFF6FF', color:'#1E40AF', fontSize:12.5, fontFamily:'Geist Mono,monospace', textTransform:'uppercase', letterSpacing:'0.08em' }}>
                <Clock size={13} /> Reply within 24 hours
              </div>
              <div style={{ marginTop:24 }}>
                <button type="button" onClick={onClose} style={{ background:'#0F172A', color:'#fff', border:'none', borderRadius:8, padding:'12px 28px', fontWeight:700, fontSize:13, letterSpacing:'0.06em', textTransform:'uppercase', cursor:'pointer' }}>Close</button>
              </div>
            </div>
          ) : (
            <>
              <h3 style={{ fontSize:20, fontWeight:800, color:'#0F172A', marginBottom:6 }}>{stepTitle[0]}</h3>
              {stepTitle[1] && <p style={{ fontSize:13.5, color:'#64748B', marginBottom:18, lineHeight:1.5 }}>{stepTitle[1]}</p>}

              {currentKey === 'service' && (
                <div style={{ display:'grid', gridTemplateColumns:'1fr 1fr', gap:10 }}>
                  {SERVICES.map(s => (
                    <IconCard key={s.id} Icon={s.Icon} label={s.label} desc={s.desc} active={answers.service === s.id} onClick={() => { set('service', s.id); setStep(1); }} />
                  ))}
                </div>
              )}

              {currentKey === 'industry' && (
                <div style={{ display:'grid', gridTemplateColumns:'repeat(3, 1fr)', gap:10 }}>
                  {INDUSTRIES.map(it => (
                    <CompactCard key={it.id} Icon={it.Icon} label={it.id} active={answers.industry === it.id} onClick={() => { set('industry', it.id); next(); }} />
                  ))}
                </div>
              )}

              {currentKey === 'platform' && (
                <div style={{ display:'grid', gridTemplateColumns:'1fr', gap:10 }}>
                  {WEB_PLATFORMS.map(p => (
                    <IconCard key={p.id} Icon={p.Icon} label={p.id} desc={p.desc} active={answers.platform === p.id} onClick={() => { set('platform', p.id); setAnswers(a => ({ ...a, wpEditor: p.id === 'WordPress' ? a.wpEditor : undefined })); next(); }} />
                  ))}
                </div>
              )}

              {currentKey === 'wpEditor' && (
                <div style={{ display:'grid', gridTemplateColumns:'1fr 1fr', gap:10 }}>
                  {WP_EDITORS.map(p => (
                    <IconCard key={p.id} Icon={p.Icon} label={p.id} desc={p.desc} active={answers.wpEditor === p.id} onClick={() => { set('wpEditor', p.id); next(); }} />
                  ))}
                </div>
              )}

              {currentKey === 'appPlatform' && (
                <div style={{ display:'grid', gridTemplateColumns:'1fr 1fr', gap:10 }}>
                  {APP_PLATFORMS.map(p => (
                    <CompactCard key={p.id} Icon={p.Icon} label={p.id} active={answers.appPlatform === p.id} onClick={() => { set('appPlatform', p.id); next(); }} />
                  ))}
                </div>
              )}

              {currentKey === 'logoKind' && (
                <div style={{ display:'grid', gridTemplateColumns:'1fr 1fr', gap:10 }}>
                  {LOGO_KINDS.map(p => (
                    <IconCard key={p.id} Icon={p.Icon} label={p.id} active={answers.logoKind === p.id} onClick={() => { set('logoKind', p.id); next(); }} />
                  ))}
                </div>
              )}

              {currentKey === 'details' && (
                <div style={{ display:'flex', flexDirection:'column', gap:14 }}>
                  <div style={{ display:'grid', gridTemplateColumns:'1fr 1fr', gap:12 }}>
                    <FieldGroup label="Your name" error={errors.name}>
                      <input type="text" value={answers.name || ''} onChange={e => set('name', e.target.value)} placeholder="Jane Doe"
                        style={inputStyle(errors.name)} />
                    </FieldGroup>
                    <FieldGroup label="Email" error={errors.email}>
                      <input type="email" value={answers.email || ''} onChange={e => set('email', e.target.value)} placeholder="you@company.com"
                        style={inputStyle(errors.email)} />
                    </FieldGroup>
                  </div>
                  <FieldGroup label="Existing site or reference link (optional)">
                    <input type="text" value={answers.existingUrl || ''} onChange={e => set('existingUrl', e.target.value)} placeholder="https://example.com"
                      style={inputStyle()} />
                  </FieldGroup>
                  <FieldGroup label="Tell us about your project">
                    <textarea value={answers.description || ''} onChange={e => set('description', e.target.value)} rows={4} placeholder="Goals, timeline, must-have features, budget range…"
                      style={{ ...inputStyle(), resize:'vertical', minHeight:96, fontFamily:'inherit' }} />
                  </FieldGroup>
                  <FieldGroup label="Attach project files (optional)" error={errors.files}>
                    <FileUploader files={answers.files || []} onChange={files => set('files', files)} onError={msg => setErrors(er => ({ ...er, files: msg }))} />
                  </FieldGroup>
                </div>
              )}
            </>
          )}
        </div>

        {/* Footer */}
        {!submitted && (
          <div style={{ padding:'14px 22px 20px', display:'flex', alignItems:'center', justifyContent:'space-between', gap:10 }}>
            <button type="button" onClick={back} disabled={step === 0}
              style={{ background:'transparent', border:'1.5px solid #E2E8F0', color: step === 0 ? '#CBD5E1' : '#475569', borderRadius:8, padding:'10px 18px', fontWeight:600, fontSize:13, cursor: step === 0 ? 'not-allowed' : 'pointer', display:'inline-flex', alignItems:'center', gap:6 }}>
              <ChevronLeft size={16} /> Back
            </button>
            {currentKey === 'details' ? (
              <div style={{ display:'flex', flexDirection:'column', alignItems:'flex-end', gap:6 }}>
                {sendError && <div style={{ fontSize:12, color:'#DC2626' }}>{sendError}</div>}
                <button type="button" onClick={submit} disabled={sending}
                  style={{ background: sending ? '#94A3B8' : '#2563EB', color:'#fff', border:'none', borderRadius:8, padding:'12px 24px', fontWeight:700, fontSize:13, letterSpacing:'0.04em', cursor: sending ? 'wait' : 'pointer', boxShadow: sending ? 'none' : '0 4px 14px rgba(37,99,235,.35)' }}>
                  {sending ? 'Sending…' : 'Send request'}
                </button>
              </div>
            ) : (
              <button type="button" onClick={next} disabled={!canAdvance}
                style={{ background: canAdvance ? '#2563EB' : '#CBD5E1', color:'#fff', border:'none', borderRadius:8, padding:'10px 22px', fontWeight:700, fontSize:13, cursor: canAdvance ? 'pointer' : 'not-allowed', display:'inline-flex', alignItems:'center', gap:6, boxShadow: canAdvance ? '0 4px 14px rgba(37,99,235,.35)' : 'none' }}>
                Next <ChevronRight size={16} />
              </button>
            )}
          </div>
        )}
      </div>
    </div>
  );
}

const MAX_FILE_BYTES = 10 * 1024 * 1024;       // 10 MB per file
const MAX_TOTAL_BYTES = 20 * 1024 * 1024;      // 20 MB total
const MAX_FILES = 5;
const ALLOWED_FILE_RE = /\.(pdf|docx?|xlsx?|pptx?|txt|csv|zip|rar|7z|png|jpe?g|gif|webp|svg|fig|sketch|psd|ai|md)$/i;

function readFileAsDataURL(file) {
  return new Promise((resolve, reject) => {
    const r = new FileReader();
    r.onload = () => resolve(r.result);
    r.onerror = () => reject(r.error || new Error('Read failed'));
    r.readAsDataURL(file);
  });
}

function fmtBytes(n) {
  if (n < 1024) return `${n} B`;
  if (n < 1024 * 1024) return `${(n / 1024).toFixed(1)} KB`;
  return `${(n / 1024 / 1024).toFixed(2)} MB`;
}

function FileUploader({ files, onChange, onError }) {
  const ref = useRef(null);
  const [busy, setBusy] = useState(false);
  const [drag, setDrag] = useState(false);

  const addFiles = async (list) => {
    const incoming = Array.from(list || []);
    if (!incoming.length) return;
    setBusy(true);
    try {
      const next = [...files];
      let total = next.reduce((s, f) => s + (f.size || 0), 0);
      for (const f of incoming) {
        if (next.length >= MAX_FILES) { onError && onError(`Max ${MAX_FILES} files`); break; }
        if (!ALLOWED_FILE_RE.test(f.name)) { onError && onError(`"${f.name}" — file type not allowed`); continue; }
        if (f.size > MAX_FILE_BYTES) { onError && onError(`"${f.name}" exceeds 10 MB`); continue; }
        if (total + f.size > MAX_TOTAL_BYTES) { onError && onError('Total size exceeds 20 MB'); break; }
        const dataUrl = await readFileAsDataURL(f);
        next.push({ name: f.name, type: f.type || 'application/octet-stream', size: f.size, dataUrl });
        total += f.size;
      }
      onChange(next);
      onError && onError(undefined);
    } catch (e) {
      onError && onError(e.message || 'Could not read file');
    } finally {
      setBusy(false);
      if (ref.current) ref.current.value = '';
    }
  };

  const remove = (i) => onChange(files.filter((_, idx) => idx !== i));

  return (
    <div>
      <div
        onClick={() => ref.current?.click()}
        onDragOver={e => { e.preventDefault(); setDrag(true); }}
        onDragLeave={() => setDrag(false)}
        onDrop={e => { e.preventDefault(); setDrag(false); addFiles(e.dataTransfer.files); }}
        style={{ cursor:'pointer', border:`2px dashed ${drag ? '#2563EB' : '#CBD5E1'}`, background: drag ? '#EFF6FF' : '#F8FAFC', borderRadius:10, padding:'18px 16px', textAlign:'center', transition:'all .15s' }}>
        <div style={{ display:'flex', flexDirection:'column', alignItems:'center', gap:6 }}>
          <Upload size={22} color={drag ? '#2563EB' : '#64748B'} />
          <div style={{ fontSize:13.5, color:'#0F172A', fontWeight:600 }}>
            {busy ? 'Reading files…' : 'Drop files here or click to browse'}
          </div>
          <div style={{ fontSize:11.5, color:'#94A3B8' }}>
            PDF, DOC, images, ZIP up to 10 MB · max {MAX_FILES} files (20 MB total)
          </div>
        </div>
        <input ref={ref} type="file" multiple onChange={e => addFiles(e.target.files)}
          accept=".pdf,.doc,.docx,.xls,.xlsx,.ppt,.pptx,.txt,.csv,.zip,.rar,.7z,.png,.jpg,.jpeg,.gif,.webp,.svg,.fig,.sketch,.psd,.ai,.md,image/*"
          style={{ display:'none' }} />
      </div>
      {files.length > 0 && (
        <ul style={{ listStyle:'none', margin:'10px 0 0', padding:0, display:'flex', flexDirection:'column', gap:6 }}>
          {files.map((f, i) => (
            <li key={i} style={{ display:'flex', alignItems:'center', gap:10, padding:'8px 12px', background:'#fff', border:'1px solid #E2E8F0', borderRadius:8 }}>
              <div style={{ width:30, height:30, borderRadius:6, background:'#EFF6FF', color:'#2563EB', display:'flex', alignItems:'center', justifyContent:'center', flexShrink:0 }}>
                <Upload size={14} />
              </div>
              <div style={{ flex:1, minWidth:0 }}>
                <div style={{ fontSize:13, color:'#0F172A', fontWeight:500, overflow:'hidden', textOverflow:'ellipsis', whiteSpace:'nowrap' }}>{f.name}</div>
                <div style={{ fontSize:11, color:'#94A3B8' }}>{fmtBytes(f.size)}</div>
              </div>
              <button type="button" onClick={() => remove(i)} aria-label={`Remove ${f.name}`}
                style={{ width:28, height:28, borderRadius:'50%', background:'transparent', border:'1.5px solid #E2E8F0', color:'#64748B', cursor:'pointer', display:'flex', alignItems:'center', justifyContent:'center', flexShrink:0 }}
                onMouseEnter={e => { e.currentTarget.style.background='#FEE2E2'; e.currentTarget.style.borderColor='#FCA5A5'; e.currentTarget.style.color='#DC2626'; }}
                onMouseLeave={e => { e.currentTarget.style.background='transparent'; e.currentTarget.style.borderColor='#E2E8F0'; e.currentTarget.style.color='#64748B'; }}>
                <X size={13} />
              </button>
            </li>
          ))}
        </ul>
      )}
    </div>
  );
}

function FieldGroup({ label, error, children }) {
  return (
    <label style={{ display:'block' }}>
      <div style={{ fontSize:11.5, fontWeight:700, color:'#475569', textTransform:'uppercase', letterSpacing:'0.08em', marginBottom:6, fontFamily:'Geist Mono,monospace', display:'flex', alignItems:'center', justifyContent:'space-between' }}>
        <span>{label}</span>
        {error && <span style={{ color:'#DC2626', textTransform:'none', letterSpacing:0, fontFamily:'inherit' }}>{error}</span>}
      </div>
      {children}
    </label>
  );
}

function inputStyle(err) {
  return {
    width:'100%', padding:'11px 14px', border:`1.5px solid ${err ? '#DC2626' : '#E2E8F0'}`, borderRadius:8, fontSize:14, color:'#0F172A', background:'#fff', outline:'none', transition:'border-color .15s, box-shadow .15s', boxSizing:'border-box',
  };
}

// ─── Lightbox Modal ───────────────────────────────────────────────────────────
function LightboxModal({ images = [], initialIndex = 0, title = '', onClose }) {
  const [index, setIndex] = useState(initialIndex);
  const total = images.length;
  const currentSrc = images[index] || '';

  const prev = useCallback((e) => {
    e?.stopPropagation();
    setIndex(i => (i - 1 + total) % total);
  }, [total]);

  const next = useCallback((e) => {
    e?.stopPropagation();
    setIndex(i => (i + 1) % total);
  }, [total]);

  useEffect(() => {
    const onKey = (e) => {
      if (e.key === 'Escape') onClose();
      if (e.key === 'ArrowLeft') prev();
      if (e.key === 'ArrowRight') next();
    };
    window.addEventListener('keydown', onKey);
    return () => window.removeEventListener('keydown', onKey);
  }, [onClose, prev, next]);

  useEffect(() => {
    const prev = document.body.style.overflow;
    document.body.style.overflow = 'hidden';
    return () => { document.body.style.overflow = prev; };
  }, []);

  return createPortal(
    <div
      style={{
        position:'fixed',
        top:0,
        left:0,
        right:0,
        bottom:0,
        width:'100vw',
        height:'100vh',
        zIndex:99999,
        background:'rgba(5, 10, 24, 0.94)',
        backdropFilter:'blur(12px)',
        WebkitBackdropFilter:'blur(12px)',
        display:'flex',
        flexDirection:'column',
        alignItems:'center',
        justifyContent:'space-between',
        padding:'16px 20px',
        animation:'fadeIn .25s ease both',
        userSelect:'none',
        boxSizing:'border-box'
      }}
      onClick={onClose}
    >
      {/* Top Bar */}
      <div
        style={{
          width:'100%',
          maxWidth:1200,
          display:'flex',
          alignItems:'center',
          justifyContent:'space-between',
          zIndex:2,
          padding:'8px 0'
        }}
        onClick={e => e.stopPropagation()}
      >
        <div style={{ display:'flex', alignItems:'center', gap:12 }}>
          <span className="mono" style={{ fontSize:12, color:'#93C5FD', fontWeight:600, background:'rgba(30,64,175,0.4)', padding:'4px 12px', borderRadius:99, border:'1px solid rgba(147,197,253,0.3)' }}>
            {index + 1} / {total}
          </span>
          {title && (
            <span style={{ fontSize:14, color:'#F1F5F9', fontWeight:600, maxWidth:'60vw', overflow:'hidden', textOverflow:'ellipsis', whiteSpace:'nowrap' }}>
              {title}
            </span>
          )}
        </div>

        <button
          onClick={onClose}
          aria-label="Close Lightbox"
          style={{
            width:40,
            height:40,
            borderRadius:'50%',
            background:'rgba(255,255,255,0.12)',
            border:'1px solid rgba(255,255,255,0.2)',
            color:'#fff',
            display:'flex',
            alignItems:'center',
            justifyContent:'center',
            cursor:'pointer',
            transition:'all .2s'
          }}
          onMouseEnter={e => { e.currentTarget.style.background = '#EF4444'; e.currentTarget.style.borderColor = '#EF4444'; }}
          onMouseLeave={e => { e.currentTarget.style.background = 'rgba(255,255,255,0.12)'; e.currentTarget.style.borderColor = 'rgba(255,255,255,0.2)'; }}
        >
          <X size={20} strokeWidth={2.5} />
        </button>
      </div>

      {/* Main Center Image Stage */}
      <div
        style={{
          position:'relative',
          width:'100%',
          flex:1,
          display:'flex',
          alignItems:'center',
          justifyContent:'center',
          minHeight:0,
          margin:'10px 0'
        }}
        onClick={e => e.stopPropagation()}
      >
        {total > 1 && (
          <button
            onClick={prev}
            aria-label="Previous Image"
            style={{
              position:'absolute',
              left:10,
              top:'50%',
              transform:'translateY(-50%)',
              width:46,
              height:46,
              borderRadius:'50%',
              background:'rgba(15,23,42,0.75)',
              border:'1px solid rgba(255,255,255,0.25)',
              color:'#fff',
              display:'flex',
              alignItems:'center',
              justifyContent:'center',
              cursor:'pointer',
              zIndex:10,
              transition:'all .2s',
              boxShadow:'0 4px 20px rgba(0,0,0,0.5)'
            }}
            onMouseEnter={e => { e.currentTarget.style.background = '#1E40AF'; e.currentTarget.style.transform = 'translateY(-50%) scale(1.08)'; }}
            onMouseLeave={e => { e.currentTarget.style.background = 'rgba(15,23,42,0.75)'; e.currentTarget.style.transform = 'translateY(-50%) scale(1)'; }}
          >
            <ChevronLeft size={24} strokeWidth={2.5} />
          </button>
        )}

        <img
          key={currentSrc}
          src={currentSrc}
          alt={`Preview ${index + 1}`}
          style={{
            maxWidth:'92vw',
            maxHeight:'74vh',
            width:'auto',
            height:'auto',
            objectFit:'contain',
            borderRadius:12,
            boxShadow:'0 20px 60px rgba(0,0,0,0.8)',
            border:'1px solid rgba(255,255,255,0.12)',
            animation:'zoomIn .25s cubic-bezier(.2,.8,.2,1) both'
          }}
        />

        {total > 1 && (
          <button
            onClick={next}
            aria-label="Next Image"
            style={{
              position:'absolute',
              right:10,
              top:'50%',
              transform:'translateY(-50%)',
              width:46,
              height:46,
              borderRadius:'50%',
              background:'rgba(15,23,42,0.75)',
              border:'1px solid rgba(255,255,255,0.25)',
              color:'#fff',
              display:'flex',
              alignItems:'center',
              justifyContent:'center',
              cursor:'pointer',
              zIndex:10,
              transition:'all .2s',
              boxShadow:'0 4px 20px rgba(0,0,0,0.5)'
            }}
            onMouseEnter={e => { e.currentTarget.style.background = '#1E40AF'; e.currentTarget.style.transform = 'translateY(-50%) scale(1.08)'; }}
            onMouseLeave={e => { e.currentTarget.style.background = 'rgba(15,23,42,0.75)'; e.currentTarget.style.transform = 'translateY(-50%) scale(1)'; }}
          >
            <ChevronRight size={24} strokeWidth={2.5} />
          </button>
        )}
      </div>

      {/* Bottom Thumbnail Strip */}
      {total > 1 && (
        <div
          style={{
            width:'100%',
            maxWidth:800,
            display:'flex',
            gap:8,
            justifyContent:'center',
            overflowX:'auto',
            padding:'10px 0 6px',
            scrollbarWidth:'none',
            zIndex:2
          }}
          onClick={e => e.stopPropagation()}
        >
          {images.map((img, i) => {
            const active = i === index;
            return (
              <button
                key={i}
                onClick={() => setIndex(i)}
                style={{
                  width:64,
                  height:46,
                  borderRadius:8,
                  overflow:'hidden',
                  border: active ? '2px solid #3B82F6' : '1.5px solid rgba(255,255,255,0.2)',
                  opacity: active ? 1 : 0.55,
                  padding:0,
                  background:'#0F172A',
                  cursor:'pointer',
                  transform: active ? 'scale(1.08)' : 'scale(1)',
                  transition:'all .2s',
                  flexShrink:0
                }}
              >
                <img src={img} alt="" style={{ width:'100%', height:'100%', objectFit:'cover' }} />
              </button>
            );
          })}
        </div>
      )}
    </div>,
    document.body
  );
}

function resolveFeatureUrl(p) {
  if (!p?.url) return '';
  let u = String(p.url).trim();
  if (u.startsWith('//')) u = 'https:' + u;
  else if (!/^https?:\/\//i.test(u)) u = 'https://' + u;
  return u;
}

// ─── Project Detail (Full Case Study Modal) ───────────────────────────────────
function ProjectDetail({ project: p, onClose, onOpenQuote }) {
  const [activePlatform, setActivePlatform] = useState(() => p.platform || (p.platforms && p.platforms[0]) || '');
  const activeImgs = (p.platformImages && activePlatform && p.platformImages[activePlatform]?.length)
    ? p.platformImages[activePlatform]
    : (p.images?.length ? p.images : (p.image ? [p.image] : ['']));
  const imgs = activeImgs;
  const parsedVideo = p.videoUrl ? parseVideo(p.videoUrl) : null;
  const isApp = p.categories?.includes('Mobile Apps') || p.type === 'app';
  const liveUrl = resolveFeatureUrl(p);

  const [showTechAudit, setShowTechAudit] = useState(true);
  const [lightboxIndex, setLightboxIndex] = useState(null);
  const [mediaMode, setMediaMode] = useState(() => (parsedVideo ? 'video' : 'gallery'));
  const [liveDevice, setLiveDevice] = useState('desktop'); // 'desktop' | 'tablet' | 'mobile'
  const [liveReloadKey, setLiveReloadKey] = useState(0);
  const [embedStatus, setEmbedStatus] = useState({ checked: false, ok: true, reason: '' });
  const videoRef = useRef(null);

  // Sync mode if project changes
  useEffect(() => {
    setActivePlatform(p?.platform || (p?.platforms && p?.platforms[0]) || '');
    setMediaMode(parsedVideo ? 'video' : 'gallery');
  }, [p?.id, p?.videoUrl]);

  // Ensure native video autoplays reliably
  useEffect(() => {
    if (mediaMode === 'video' && videoRef.current) {
      videoRef.current.defaultMuted = true;
      videoRef.current.muted = true;
      const playPromise = videoRef.current.play();
      if (playPromise !== undefined) {
        playPromise.catch(() => {});
      }
    }
  }, [mediaMode, parsedVideo?.src]);

  // Lock background body scroll while modal is active
  useEffect(() => {
    const prevOverflow = document.body.style.overflow;
    document.body.style.overflow = 'hidden';
    return () => {
      document.body.style.overflow = prevOverflow;
    };
  }, []);

  // Keyboard escape listener
  useEffect(() => {
    const onKey = (e) => {
      if (e.key === 'Escape') onClose();
    };
    window.addEventListener('keydown', onKey);
    return () => window.removeEventListener('keydown', onKey);
  }, [onClose]);

  useEffect(() => {
    if (!liveUrl) return;
    let cancelled = false;
    fetch(`/api/embed-check?url=${encodeURIComponent(liveUrl)}`)
      .then(r => r.json())
      .then(j => {
        if (!cancelled) setEmbedStatus({ checked: true, ok: !!j.embeddable, reason: j.reason || '' });
      })
      .catch(() => {
        if (!cancelled) setEmbedStatus({ checked: true, ok: true, reason: '' });
      });
    return () => { cancelled = true; };
  }, [liveUrl]);

  return createPortal(
    <div
      style={{
        position:'fixed',
        top:0,
        left:0,
        right:0,
        bottom:0,
        width:'100vw',
        height:'100vh',
        zIndex:9999,
        background:'rgba(15,23,42,.85)',
        backdropFilter:'blur(8px)',
        WebkitBackdropFilter:'blur(8px)',
        display:'flex',
        alignItems:'flex-start',
        justifyContent:'center',
        padding:'16px 12px',
        overflowY:'auto',
        boxSizing:'border-box'
      }}
      onClick={onClose}
    >
      <div
        className="anim-fadeUp"
        style={{
          width:'100%',
          maxWidth:960,
          background:'#F0F7FF',
          borderRadius:22,
          overflow:'hidden',
          boxShadow:'0 36px 90px rgba(30,64,175,.35)',
          marginBottom:24,
          border:'1px solid #BFDBFE'
        }}
        onClick={e => e.stopPropagation()}
      >
        {/* Sticky Window Header */}
        <div style={{ background:'#1E3A8A' }}>
          <div className="browser-bar" style={{ padding:'10px 16px', display:'flex', alignItems:'center', gap:10, flexWrap:'wrap' }}>
            <div style={{ display:'flex', gap:6, alignItems:'center', flexShrink:0 }}>
              {['#F87171','#FBBF24','#34D399'].map(c => (
                <span key={c} style={{ width:11, height:11, borderRadius:'50%', background:c, display:'inline-block' }} />
              ))}
            </div>
            
            {/* Clickable Address Bar */}
            <div
              onClick={() => { if (liveUrl) setMediaMode('live'); }}
              title={liveUrl ? "Click to preview live application inside popup" : undefined}
              style={{
                flex:1,
                minWidth:190,
                background:'#FFFFFF',
                borderRadius:8,
                padding:'6px 14px',
                fontFamily:'Geist Mono,monospace',
                fontSize:12,
                color:'#1E293B',
                overflow:'hidden',
                textOverflow:'ellipsis',
                whiteSpace:'nowrap',
                border: mediaMode === 'live' ? '1.5px solid #2563EB' : '1px solid #BFDBFE',
                display:'flex',
                alignItems:'center',
                gap:8,
                cursor: liveUrl ? 'pointer' : 'default',
                boxShadow:'0 1px 3px rgba(30,64,175,.08)',
                transition:'all .15s'
              }}
            >
              <Globe size={13} color={mediaMode === 'live' ? '#2563EB' : '#64748B'} />
              <span style={{ overflow:'hidden', textOverflow:'ellipsis', whiteSpace:'nowrap', fontWeight: mediaMode === 'live' ? 700 : 500 }}>
                {liveUrl || (isApp ? 'mobile-app.techpenta.com' : `techpenta.com/projects/${p.id}`)}
              </span>
              {liveUrl && (
                <span style={{
                  fontSize:10,
                  padding:'2px 8px',
                  borderRadius:99,
                  background: mediaMode === 'live' ? '#EFF6FF' : '#F1F5F9',
                  color: mediaMode === 'live' ? '#1D4ED8' : '#64748B',
                  fontWeight:700,
                  marginLeft:'auto',
                  flexShrink:0
                }}>
                  {mediaMode === 'live' ? '● Browsing Live' : 'Click to Browse'}
                </span>
              )}
            </div>

            {/* Media Mode Toggle Tabs */}
            <div style={{ display:'flex', alignItems:'center', gap:3, background:'rgba(255,255,255,0.92)', padding:3, borderRadius:99, border:'1px solid #BFDBFE' }}>
              {parsedVideo && (
                <button
                  type="button"
                  onClick={() => setMediaMode('video')}
                  style={{
                    display:'inline-flex',
                    alignItems:'center',
                    gap:6,
                    padding:'5px 12px',
                    borderRadius:99,
                    border:'none',
                    background: mediaMode === 'video' ? '#1E40AF' : 'transparent',
                    color: mediaMode === 'video' ? '#FFFFFF' : '#1E40AF',
                    fontSize:11.5,
                    fontWeight:700,
                    cursor:'pointer',
                    transition:'all .15s'
                  }}
                >
                  <Film size={12} />
                  <span>Video Demo</span>
                  {mediaMode === 'video' && (
                    <span style={{ width:6, height:6, borderRadius:'50%', background:'#34D399', boxShadow:'0 0 6px #34D399', display:'inline-block' }} />
                  )}
                </button>
              )}

              <button
                type="button"
                onClick={() => setMediaMode('gallery')}
                style={{
                  display:'inline-flex',
                  alignItems:'center',
                  gap:5,
                  padding:'5px 12px',
                  borderRadius:99,
                  border:'none',
                  background: mediaMode === 'gallery' ? '#1E40AF' : 'transparent',
                  color: mediaMode === 'gallery' ? '#FFFFFF' : '#475569',
                  fontSize:11.5,
                  fontWeight:600,
                  cursor:'pointer',
                  transition:'all .15s'
                }}
              >
                <Eye size={12} />
                <span>Gallery {imgs.length > 1 ? `(${imgs.length})` : ''}</span>
              </button>

              {liveUrl && (
                <button
                  type="button"
                  onClick={() => setMediaMode('live')}
                  style={{
                    display:'inline-flex',
                    alignItems:'center',
                    gap:5,
                    padding:'5px 12px',
                    borderRadius:99,
                    border:'none',
                    background: mediaMode === 'live' ? '#2563EB' : 'transparent',
                    color: mediaMode === 'live' ? '#FFFFFF' : '#1E40AF',
                    fontSize:11.5,
                    fontWeight:700,
                    cursor:'pointer',
                    transition:'all .15s'
                  }}
                >
                  <Globe size={12} />
                  <span>Browse Live</span>
                </button>
              )}
            </div>

            {/* Visit Live Site Button */}
            {liveUrl && (
              <a
                href={liveUrl}
                target="_blank"
                rel="noopener noreferrer"
                className="mono"
                title="Open live site in separate tab"
                style={{
                  display:'inline-flex',
                  alignItems:'center',
                  gap:5,
                  padding:'6px 14px',
                  borderRadius:99,
                  background:'#2563EB',
                  color:'#FFFFFF',
                  fontSize:11.5,
                  textDecoration:'none',
                  fontWeight:700,
                  boxShadow:'0 2px 8px rgba(37,99,235,.35)',
                  whiteSpace:'nowrap',
                  transition:'all .15s'
                }}
                onMouseEnter={e => e.currentTarget.style.background = '#1D4ED8'}
                onMouseLeave={e => e.currentTarget.style.background = '#2563EB'}
              >
                <span>Visit Live Site</span>
                <ExternalLink size={12} strokeWidth={2.4} />
              </a>
            )}

            {/* Modal Close Button */}
            <button
              onClick={onClose}
              aria-label="Close modal"
              style={{
                width:34,
                height:34,
                borderRadius:'50%',
                background:'rgba(255,255,255,.9)',
                border:'1px solid #BFDBFE',
                cursor:'pointer',
                color:'#1E3A8A',
                display:'flex',
                alignItems:'center',
                justifyContent:'center',
                flexShrink:0,
                transition:'all .15s'
              }}
              onMouseEnter={e => { e.currentTarget.style.background = '#EF4444'; e.currentTarget.style.color = '#fff'; }}
              onMouseLeave={e => { e.currentTarget.style.background = 'rgba(255,255,255,.9)'; e.currentTarget.style.color = '#1E3A8A'; }}
            >
              <X size={16} strokeWidth={2.5} />
            </button>
          </div>

          {/* Media Header (Interactive: Gallery | Live Browser | Video) */}
          {mediaMode === 'live' && liveUrl && (
            <div style={{ background:'#0B1220', borderTop:'1px solid rgba(255,255,255,.1)' }}>
              {/* In-Modal Browser Controls */}
              <div style={{ display:'flex', alignItems:'center', justifyContent:'space-between', padding:'8px 16px', background:'#0F172A', borderBottom:'1px solid rgba(255,255,255,.1)', gap:10, flexWrap:'wrap' }}>
                <div style={{ display:'flex', alignItems:'center', gap:6 }}>
                  <span className="mono" style={{ fontSize:10.5, color:'#94A3B8', textTransform:'uppercase', letterSpacing:'0.06em', marginRight:4 }}>
                    Viewport:
                  </span>
                  {[
                    { key:'desktop', label:'Desktop', Icon: Monitor },
                    { key:'tablet', label:'Tablet (768px)', Icon: Tablet },
                    { key:'mobile', label:'Mobile (375px)', Icon: Smartphone },
                  ].map(dev => {
                    const active = liveDevice === dev.key;
                    return (
                      <button
                        key={dev.key}
                        type="button"
                        onClick={() => setLiveDevice(dev.key)}
                        style={{
                          display:'inline-flex',
                          alignItems:'center',
                          gap:5,
                          padding:'4px 10px',
                          borderRadius:6,
                          border: active ? '1px solid #3B82F6' : '1px solid rgba(255,255,255,.15)',
                          background: active ? '#1E40AF' : 'rgba(255,255,255,.05)',
                          color: active ? '#fff' : '#94A3B8',
                          fontSize:11,
                          fontWeight:600,
                          cursor:'pointer',
                          transition:'all .15s'
                        }}
                      >
                        <dev.Icon size={12} />
                        <span>{dev.label}</span>
                      </button>
                    );
                  })}
                </div>

                <div style={{ display:'flex', alignItems:'center', gap:8 }}>
                  <button
                    type="button"
                    onClick={() => setLiveReloadKey(k => k + 1)}
                    title="Reload live preview"
                    className="mono"
                    style={{
                      display:'inline-flex',
                      alignItems:'center',
                      gap:4,
                      padding:'4px 10px',
                      borderRadius:6,
                      background:'rgba(255,255,255,.08)',
                      border:'1px solid rgba(255,255,255,.15)',
                      color:'#CBD5E1',
                      fontSize:11,
                      cursor:'pointer'
                    }}
                  >
                    ↻ Reload
                  </button>
                  <a
                    href={liveUrl}
                    target="_blank"
                    rel="noopener noreferrer"
                    className="mono"
                    style={{
                      display:'inline-flex',
                      alignItems:'center',
                      gap:4,
                      padding:'4px 10px',
                      borderRadius:6,
                      background:'#2563EB',
                      color:'#fff',
                      fontSize:11,
                      fontWeight:600,
                      textDecoration:'none'
                    }}
                  >
                    Open Tab ↗
                  </a>
                </div>
              </div>

              {/* Live Iframe Stage or Security Fallback Card */}
              {embedStatus.checked && !embedStatus.ok ? (
                <div style={{ padding:'44px 24px', textAlign:'center', color:'#fff', display:'flex', flexDirection:'column', alignItems:'center', justifyContent:'center', minHeight:440 }}>
                  <div style={{ width:56, height:56, borderRadius:'50%', background:'rgba(96,165,250,.18)', color:'#60A5FA', display:'flex', alignItems:'center', justifyContent:'center', marginBottom:16 }}>
                    <Shield size={28} />
                  </div>
                  <h3 className="display" style={{ fontSize:22, color:'#fff', marginBottom:8, lineHeight:1.25 }}>
                    Live Storefront: {p.title}
                  </h3>
                  <p style={{ fontSize:14, color:'#93C5FD', maxWidth:520, margin:'0 auto 22px', lineHeight:1.6 }}>
                    This external production storefront ({liveUrl.replace(/^https?:\/\//,'').replace(/\/$/,'')}) protects visitor sessions with security headers (<code style={{ background:'rgba(255,255,255,.12)', padding:'2px 6px', borderRadius:4, fontFamily:'Geist Mono,monospace', color:'#FDE047' }}>X-Frame-Options: {embedStatus.reason || 'DENY'}</code>).
                    <br />You can explore the live app directly in a full browser window.
                  </p>
                  <div style={{ display:'flex', gap:12, flexWrap:'wrap', justifyContent:'center' }}>
                    <a
                      href={liveUrl}
                      target="_blank"
                      rel="noopener noreferrer"
                      className="mono"
                      style={{
                        display:'inline-flex',
                        alignItems:'center',
                        gap:8,
                        padding:'12px 26px',
                        borderRadius:99,
                        background:'linear-gradient(135deg, #2563EB, #1D4ED8)',
                        color:'#fff',
                        fontSize:12.5,
                        fontWeight:700,
                        textDecoration:'none',
                        textTransform:'uppercase',
                        letterSpacing:'0.06em',
                        boxShadow:'0 8px 24px rgba(37,99,235,.4)'
                      }}
                    >
                      <span>Launch Live Application ↗</span>
                    </a>
                    <button
                      type="button"
                      onClick={() => setMediaMode('gallery')}
                      className="mono"
                      style={{
                        padding:'12px 22px',
                        borderRadius:99,
                        background:'rgba(255,255,255,.08)',
                        border:'1px solid rgba(255,255,255,.2)',
                        color:'#DBEAFE',
                        fontSize:12,
                        fontWeight:600,
                        cursor:'pointer'
                      }}
                    >
                      ← Back to Visual Gallery
                    </button>
                  </div>
                </div>
              ) : (
                <div style={{ padding: liveDevice === 'desktop' ? 0 : '20px 14px', display:'flex', justifyContent:'center', alignItems:'center', background:'#070E1E' }}>
                  <iframe
                    key={`${liveUrl}-${liveDevice}-${liveReloadKey}`}
                    src={liveUrl}
                    title={`${p.title} Live Application`}
                    style={{
                      width: liveDevice === 'mobile' ? 375 : liveDevice === 'tablet' ? 768 : '100%',
                      height: 480,
                      maxWidth: '100%',
                      border: 'none',
                      borderRadius: liveDevice === 'desktop' ? 0 : 12,
                      boxShadow: liveDevice === 'desktop' ? 'none' : '0 18px 48px rgba(0,0,0,0.6)',
                      background: '#fff'
                    }}
                    sandbox="allow-scripts allow-same-origin allow-forms allow-popups"
                  />
                </div>
              )}
            </div>
          )}

          {mediaMode === 'video' && parsedVideo && (
            <div style={{ position:'relative', width:'100%', maxHeight:500, background:'#070E1E', display:'flex', alignItems:'center', justifyContent:'center', minHeight:320, overflow:'hidden' }}>
              {parsedVideo.type === 'youtube' && (
                <iframe
                  src={parsedVideo.src.includes('?') ? `${parsedVideo.src}&autoplay=1&mute=1&loop=1` : `${parsedVideo.src}?autoplay=1&mute=1&loop=1`}
                  title={`${p.title} video`}
                  style={{ width:'100%', height:480, maxHeight:500, border:'none', display:'block' }}
                  allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture"
                  allowFullScreen
                />
              )}
              {parsedVideo.type === 'vimeo' && (
                <iframe
                  src={parsedVideo.src.includes('?') ? `${parsedVideo.src}&autoplay=1&muted=1&loop=1` : `${parsedVideo.src}?autoplay=1&muted=1&loop=1`}
                  title={`${p.title} video`}
                  style={{ width:'100%', height:480, maxHeight:500, border:'none', display:'block' }}
                  allow="autoplay; fullscreen; picture-in-picture"
                  allowFullScreen
                />
              )}
              {parsedVideo.type === 'video' && (
                <div style={{ position:'relative', width:'100%', height:'100%', display:'flex', alignItems:'center', justifyContent:'center', background:'#070E1E' }}>
                  <video
                    ref={videoRef}
                    key={parsedVideo.src}
                    src={parsedVideo.src}
                    controls
                    playsInline
                    autoPlay
                    muted
                    defaultMuted
                    loop
                    preload="auto"
                    style={{ width:'100%', maxHeight:500, objectFit:'contain', background:'#070E1E', display:'block' }}
                  />
                  <div className="mono" style={{ position:'absolute', right:12, bottom:14, zIndex:3, background:'rgba(15,23,42,0.85)', backdropFilter:'blur(8px)', color:'#93C5FD', padding:'4px 12px', borderRadius:99, fontSize:10.5, fontWeight:700, letterSpacing:'0.06em', border:'1px solid rgba(147,197,253,0.3)', pointerEvents:'none', display:'flex', alignItems:'center', gap:6 }}>
                    <span style={{ width:6, height:6, borderRadius:'50%', background:'#34D399', boxShadow:'0 0 8px #34D399' }} />
                    Techpenta Showcase
                  </div>
                </div>
              )}
            </div>
          )}

          {mediaMode === 'gallery' && (
            <div style={{ position:'relative', maxHeight: isApp ? 540 : 460, overflow:'hidden', background:'#0F172A' }}>
              {parsedVideo && (
                <button
                  type="button"
                  onClick={() => setMediaMode('video')}
                  style={{
                    position:'absolute',
                    top:12,
                    left:12,
                    zIndex:8,
                    background:'linear-gradient(135deg, #1E40AF, #2563EB)',
                    color:'#fff',
                    padding:'6px 14px',
                    borderRadius:99,
                    border:'1px solid rgba(255,255,255,0.3)',
                    fontSize:11.5,
                    fontWeight:700,
                    cursor:'pointer',
                    display:'flex',
                    alignItems:'center',
                    gap:6,
                    boxShadow:'0 4px 16px rgba(30,64,175,0.4)',
                    transition:'all .15s'
                  }}
                  onMouseEnter={e => { e.currentTarget.style.transform = 'scale(1.04)'; }}
                  onMouseLeave={e => { e.currentTarget.style.transform = 'scale(1)'; }}
                >
                  <Film size={13} />
                  <span>▶ Play Video Demo</span>
                </button>
              )}
              {p.platformImages && Object.keys(p.platformImages).length > 1 && (
                <div style={{ padding:'10px 16px', background:'#FFFFFF', borderBottom:'1px solid #DBEAFE', display:'flex', alignItems:'center', gap:10, flexWrap:'wrap', zIndex:9, position:'relative' }}>
                  <span className="mono" style={{ fontSize:10.5, color:'#64748B', fontWeight:700, textTransform:'uppercase', letterSpacing:'0.06em' }}>
                    Platform Screenshots:
                  </span>
                  <div style={{ display:'flex', gap:6, flexWrap:'wrap' }}>
                    {Object.keys(p.platformImages).map(plat => {
                      const isCur = activePlatform === plat;
                      const count = p.platformImages[plat]?.length || 0;
                      return (
                        <button
                          key={plat}
                          type="button"
                          onClick={() => setActivePlatform(plat)}
                          className="mono"
                          style={{
                            display:'inline-flex',
                            alignItems:'center',
                            gap:5,
                            padding:'4px 11px',
                            borderRadius:99,
                            border: isCur ? '1.5px solid #1E40AF' : '1px solid #CBD5E1',
                            background: isCur ? '#1E40AF' : '#F8FAFC',
                            color: isCur ? '#FFFFFF' : '#334155',
                            fontWeight: isCur ? 700 : 500,
                            fontSize:11,
                            cursor:'pointer',
                            transition:'all .15s'
                          }}
                        >
                          <span>{plat === 'MacBook' ? '' : plat === 'Linux' ? '🐧' : plat === 'Windows' ? '⊞' : '📱'}</span>
                          <span>{plat} ({count})</span>
                        </button>
                      );
                    })}
                  </div>
                </div>
              )}
              <Carousel images={imgs} aspectRatio={isApp ? '66%' : '54%'} autoPlay={true} showNumber={true} fit="contain" onImageClick={(currIdx) => setLightboxIndex(currIdx)} />
              <button
                type="button"
                onClick={() => setLightboxIndex(0)}
                style={{
                  position:'absolute',
                  bottom:12,
                  right:12,
                  zIndex:8,
                  background:'rgba(15,23,42,0.85)',
                  backdropFilter:'blur(8px)',
                  color:'#fff',
                  padding:'6px 14px',
                  borderRadius:99,
                  border:'1px solid rgba(255,255,255,0.25)',
                  fontSize:11,
                  fontWeight:600,
                  cursor:'pointer',
                  display:'flex',
                  alignItems:'center',
                  gap:6,
                  transition:'all .15s'
                }}
                onMouseEnter={e => { e.currentTarget.style.background = '#1E40AF'; }}
                onMouseLeave={e => { e.currentTarget.style.background = 'rgba(15,23,42,0.85)'; }}
              >
                <Eye size={13} />
                <span>Enlarge Slides</span>
              </button>
            </div>
          )}
        </div>

        {/* Case Study Meta & Action Bar */}
        <div style={{ padding:'26px 36px 20px', background:'#FFFFFF', borderBottom:'1px solid #DBEAFE' }}>
          <div style={{ display:'flex', flexWrap:'wrap', justifyContent:'space-between', alignItems:'flex-start', gap:16, marginBottom:12 }}>
            <div>
              <div style={{ display:'flex', alignItems:'center', gap:8, flexWrap:'wrap', marginBottom:8 }}>
                <span className="mono" style={{ fontSize:10.5, padding:'3px 10px', background:'#1E40AF', color:'#fff', borderRadius:99, fontWeight:600, textTransform:'uppercase' }}>
                  {p.displayType || p.siteType}
                </span>
                {p.platform && (
                  <span className="mono" style={{
                    fontSize:10.5,
                    padding:'3px 10px',
                    background: /macbook|macos/i.test(p.platform) ? '#F1F5F9' : /linux/i.test(p.platform) ? '#FEF3C7' : /windows/i.test(p.platform) ? '#E0F2FE' : '#F5F3FF',
                    color: /macbook|macos/i.test(p.platform) ? '#334155' : /linux/i.test(p.platform) ? '#B45309' : /windows/i.test(p.platform) ? '#0369A1' : '#6D28D9',
                    border: '1px solid ' + (/macbook|macos/i.test(p.platform) ? '#CBD5E1' : /linux/i.test(p.platform) ? '#FDE68A' : /windows/i.test(p.platform) ? '#BAE6FD' : '#DDD6FE'),
                    borderRadius:99,
                    fontWeight:700,
                    display:'inline-flex',
                    alignItems:'center',
                    gap:4
                  }}>
                    {/macbook|macos/i.test(p.platform) && ' '}
                    {/linux/i.test(p.platform) && '🐧 '}
                    {/windows/i.test(p.platform) && '⊞ '}
                    {/ios/i.test(p.platform) && '🍎 '}
                    {/android/i.test(p.platform) && '🤖 '}
                    Platform: {p.platform}
                  </span>
                )}
                <span className="mono" style={{ fontSize:10.5, padding:'3px 10px', background:'#EFF6FF', color:'#1E40AF', border:'1px solid #BFDBFE', borderRadius:99, fontWeight:600 }}>
                  Industry: {p.industry || p.siteType}
                </span>
                <span className="mono" style={{ fontSize:10.5, color:'#64748B' }}>
                  Client: {p.client || p.name || p.title} · {p.year}
                </span>
              </div>

              <h2 className="display" style={{ fontSize:'clamp(1.9rem,3.8vw,2.8rem)', color:'#0F172A', margin:'0 0 6px', lineHeight:1.2 }}>
                {p.displayTitle || p.title}
              </h2>
              <p style={{ fontSize:15, color:'#475569', lineHeight:1.5, margin:0 }}>
                {p.businessSummary || p.tagline}
              </p>
            </div>

            {/* Quick Consultation CTA & Live Browser Link */}
            <div style={{ flexShrink:0, display:'flex', gap:10, flexWrap:'wrap', alignItems:'center' }}>
              {liveUrl && (
                <button
                  type="button"
                  onClick={() => {
                    setMediaMode('live');
                    const modalEl = document.querySelector('.anim-fadeUp');
                    if (modalEl) modalEl.scrollIntoView({ behavior:'smooth', block:'start' });
                  }}
                  className="mono"
                  style={{
                    display:'inline-flex',
                    alignItems:'center',
                    gap:6,
                    padding:'11px 18px',
                    borderRadius:99,
                    border: mediaMode === 'live' ? '1.5px solid #2563EB' : '1.5px solid #BFDBFE',
                    background: mediaMode === 'live' ? '#EFF6FF' : '#FFFFFF',
                    color: '#1E40AF',
                    fontSize:12,
                    fontWeight:700,
                    textTransform:'uppercase',
                    letterSpacing:'0.06em',
                    cursor:'pointer',
                    transition:'all .15s'
                  }}
                  onMouseEnter={e => { if (mediaMode !== 'live') e.currentTarget.style.background = '#F0F9FF'; }}
                  onMouseLeave={e => { if (mediaMode !== 'live') e.currentTarget.style.background = '#FFFFFF'; }}
                >
                  <Globe size={14} color="#2563EB" />
                  <span>Browse Live App</span>
                </button>
              )}
              <button
                onClick={() => onOpenQuote && onOpenQuote(p)}
                className="btn-primary mono"
                style={{ display:'inline-flex', alignItems:'center', gap:8, padding:'12px 24px', borderRadius:99, fontSize:12, textTransform:'uppercase', letterSpacing:'0.08em', cursor:'pointer', boxShadow:'0 8px 20px rgba(30,64,175,.25)' }}
              >
                Discuss a Project Like This <ArrowUpRight size={15} />
              </button>
            </div>
          </div>

          {/* 4 Outcome Stat Highlights */}
          <div style={{ display:'grid', gridTemplateColumns:'repeat(auto-fit, minmax(180px, 1fr))', gap:12, marginTop:20 }}>
            <div style={{ background:'#F8FAFC', border:'1px solid #DBEAFE', borderRadius:14, padding:'14px 16px', textAlign:'center' }}>
              <div className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#059669', fontWeight:700, marginBottom:4 }}>Key Business Result</div>
              <div style={{ fontSize:18, fontWeight:800, color:'#0F172A' }}>{p.impact || 'Delivered on Schedule'}</div>
            </div>
            <div style={{ background:'#F8FAFC', border:'1px solid #DBEAFE', borderRadius:14, padding:'14px 16px', textAlign:'center' }}>
              <div className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#2563EB', fontWeight:700, marginBottom:4 }}>Warranty Included</div>
              <div style={{ fontSize:18, fontWeight:800, color:'#0F172A' }}>180 Days Free Support</div>
            </div>
            <div style={{ background:'#F8FAFC', border:'1px solid #DBEAFE', borderRadius:14, padding:'14px 16px', textAlign:'center' }}>
              <div className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#7C3AED', fontWeight:700, marginBottom:4 }}>Device Compatibility</div>
              <div style={{ fontSize:18, fontWeight:800, color:'#0F172A' }}>100% Responsive</div>
            </div>
            <div style={{ background:'#F8FAFC', border:'1px solid #DBEAFE', borderRadius:14, padding:'14px 16px', textAlign:'center' }}>
              <div className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#D97706', fontWeight:700, marginBottom:4 }}>Security & Uptime</div>
              <div style={{ fontSize:18, fontWeight:800, color:'#0F172A' }}>Enterprise SSL</div>
            </div>
          </div>
        </div>

        {/* Modal Story Body */}
        <div style={{ padding:'30px 36px 36px' }}>
          
          {/* Challenge vs Solution Detailed Cards */}
          <div style={{ display:'grid', gridTemplateColumns:'repeat(auto-fit, minmax(320px, 1fr))', gap:20, marginBottom:28 }}>
            {/* The Challenge */}
            <div style={{ background:'#FFFFFF', border:'1.5px solid #FECACA', borderRadius:16, padding:22, boxShadow:'0 4px 16px rgba(220,38,38,.04)' }}>
              <div style={{ display:'flex', alignItems:'center', gap:8, marginBottom:10 }}>
                <span style={{ width:28, height:28, borderRadius:'50%', background:'#FEE2E2', color:'#DC2626', display:'flex', alignItems:'center', justifyContent:'center', fontWeight:800, fontSize:14 }}>✕</span>
                <h4 style={{ fontSize:16, fontWeight:700, color:'#991B1B', margin:0 }}>The Business Challenge</h4>
              </div>
              <p style={{ fontSize:13.5, color:'#475569', lineHeight:1.6, margin:0 }}>
                {p.challenge}
              </p>
            </div>

            {/* Our Solution */}
            <div style={{ background:'#FFFFFF', border:'1.5px solid #A7F3D0', borderRadius:16, padding:22, boxShadow:'0 4px 16px rgba(5,150,105,.04)' }}>
              <div style={{ display:'flex', alignItems:'center', gap:8, marginBottom:10 }}>
                <span style={{ width:28, height:28, borderRadius:'50%', background:'#D1FAE5', color:'#059669', display:'flex', alignItems:'center', justifyContent:'center', fontWeight:800, fontSize:14 }}>✓</span>
                <h4 style={{ fontSize:16, fontWeight:700, color:'#065F46', margin:0 }}>The TechPenta Solution</h4>
              </div>
              <p style={{ fontSize:13.5, color:'#475569', lineHeight:1.6, margin:0 }}>
                {p.solution}
              </p>
            </div>
          </div>

          {/* Key Features Delivered */}
          {p.keyFeatures && p.keyFeatures.length > 0 && (
            <div style={{ background:'#FFFFFF', border:'1px solid #DBEAFE', borderRadius:18, padding:24, marginBottom:28 }}>
              <h4 className="mono" style={{ fontSize:12, textTransform:'uppercase', letterSpacing:'0.12em', color:'#1E40AF', fontWeight:700, marginBottom:16 }}>
                ✦ Key Features & Capabilities Built:
              </h4>
              <div style={{ display:'grid', gridTemplateColumns:'repeat(auto-fit, minmax(220px, 1fr))', gap:14 }}>
                {p.keyFeatures.map((feat, idx) => (
                  <div key={idx} style={{ display:'flex', alignItems:'flex-start', gap:10, padding:'10px 14px', background:'#F8FAFC', borderRadius:10, border:'1px solid #E2E8F0' }}>
                    <CheckCircle2 size={16} style={{ color:'#059669', flexShrink:0, marginTop:2 }} />
                    <span style={{ fontSize:13, fontWeight:600, color:'#0F172A' }}>{feat}</span>
                  </div>
                ))}
              </div>
            </div>
          )}

          {/* Business Impact Narrative */}
          {p.impactDetails && (
            <div style={{ background:'linear-gradient(135deg, #EFF6FF 0%, #DBEAFE 100%)', border:'1px solid #BFDBFE', borderRadius:16, padding:'20px 24px', marginBottom:28, display:'flex', alignItems:'center', gap:16 }}>
              <div style={{ fontSize:32 }}>📈</div>
              <div>
                <div className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.1em', color:'#1E40AF', fontWeight:700, marginBottom:4 }}>
                  Business Outcome & Long-Term Value:
                </div>
                <div style={{ fontSize:14, color:'#1E3A8A', lineHeight:1.5, fontWeight:500 }}>
                  {p.impactDetails}
                </div>
              </div>
            </div>
          )}

          {/* Visual Screenshots Gallery */}
          {imgs.length > 1 && (
            <div style={{ background:'#FFFFFF', border:'1px solid #DBEAFE', borderRadius:18, padding:24, marginBottom:28 }}>
              <div style={{ display:'flex', justifyContent:'space-between', alignItems:'center', marginBottom:14 }}>
                <h4 className="mono" style={{ fontSize:12, textTransform:'uppercase', letterSpacing:'0.12em', color:'#1E40AF', fontWeight:700, margin:0 }}>
                  📷 Project Design Previews ({imgs.length} Images):
                </h4>
                <span className="mono" style={{ fontSize:10.5, color:'#64748B' }}>
                  Click to enlarge in lightbox
                </span>
              </div>
              <div style={{ display:'grid', gridTemplateColumns:'repeat(auto-fill, minmax(140px, 1fr))', gap:10 }}>
                {imgs.map((src, idx) => (
                  <button
                    key={idx}
                    type="button"
                    onClick={() => setLightboxIndex(idx)}
                    style={{
                      display:'block',
                      width:'100%',
                      borderRadius:10,
                      overflow:'hidden',
                      border:'1.5px solid #CBD5E1',
                      height:92,
                      background:'#0F172A',
                      padding:0,
                      cursor:'pointer',
                      position:'relative',
                      transition:'all .2s'
                    }}
                    onMouseEnter={e => { e.currentTarget.style.borderColor = '#2563EB'; e.currentTarget.style.transform = 'translateY(-2px)'; e.currentTarget.style.boxShadow = '0 6px 16px rgba(37,99,235,.2)'; }}
                    onMouseLeave={e => { e.currentTarget.style.borderColor = '#CBD5E1'; e.currentTarget.style.transform = 'translateY(0)'; e.currentTarget.style.boxShadow = 'none'; }}
                  >
                    <img src={src} alt={`${p.title} preview ${idx+1}`} style={{ width:'100%', height:'100%', objectFit:'cover' }} />
                    <span style={{ position:'absolute', bottom:4, right:6, background:'rgba(15,23,42,0.8)', color:'#fff', padding:'2px 6px', borderRadius:4, fontSize:10, fontFamily:'Geist Mono,monospace', fontWeight:600 }}>
                      #{idx+1}
                    </span>
                  </button>
                ))}
              </div>
            </div>
          )}

          {/* Technology Overview (Secondary & Friendly) */}
          <div style={{ background:'#FFFFFF', border:'1px solid #DBEAFE', borderRadius:18, padding:22, marginBottom:28 }}>
            <div style={{ display:'flex', justifyContent:'space-between', alignItems:'center', marginBottom:12 }}>
              <h4 className="mono" style={{ fontSize:12, textTransform:'uppercase', letterSpacing:'0.12em', color:'#64748B', fontWeight:700 }}>
                Technologies & Tools Used:
              </h4>
              <button
                onClick={() => setShowTechAudit(!showTechAudit)}
                className="mono"
                style={{ fontSize:11, color:'#2563EB', background:'none', border:'none', cursor:'pointer', textDecoration:'underline' }}
              >
                {showTechAudit ? 'Hide Technical Audit ▲' : 'View Technical Audit & Lighthouse Scores ▼'}
              </button>
            </div>

            <div style={{ display:'flex', flexWrap:'wrap', gap:6 }}>
              {(p.tags || []).map(t => (
                <span
                  key={t}
                  className="mono"
                  style={{
                    fontSize:11,
                    padding:'4px 12px',
                    borderRadius:99,
                    background:'#EFF6FF',
                    color:'#1E40AF',
                    border:'1px solid #BFDBFE',
                    fontWeight:600
                  }}
                >
                  {t}
                </span>
              ))}
            </div>

            {/* Collapsible Technical Audit for Technical Reviewers */}
            {showTechAudit && (
              <div style={{ marginTop:20, paddingTop:16, borderTop:'1px solid #E2E8F0' }}>
                {(p.type === 'website' || p.type === 'tool') && <WebsiteReport project={p} />}
                {p.type === 'logo' && <LogoView project={p} />}
                {p.type === 'seo' && <SeoView project={p} />}
                {p.type === 'app' && <AppView project={p} />}
              </div>
            )}
          </div>

          {/* Bottom Conversion Box */}
          <div style={{
            textAlign:'center',
            padding:'28px 24px',
            background:'linear-gradient(135deg, #1E3A8A 0%, #1E40AF 100%)',
            borderRadius:18,
            color:'#fff',
            boxShadow:'0 12px 30px rgba(30,64,175,.2)'
          }}>
            <div className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.15em', color:'#93C5FD', fontWeight:700, marginBottom:8 }}>
              ✦ Want Similar Results for Your Business?
            </div>
            <h3 className="display" style={{ fontSize:22, color:'#fff', margin:'0 0 8px' }}>
              Let's create something remarkable together.
            </h3>
            <p style={{ fontSize:13.5, color:'#DBEAFE', maxWidth:520, margin:'0 auto 20px', lineHeight:1.5 }}>
              Talk with our senior engineering team. We'll analyze your requirements, recommend the ideal architecture, and provide a fixed-price quote with zero commitment.
            </p>
            <div style={{ display:'flex', gap:10, justifyContent:'center', flexWrap:'wrap' }}>
              <button
                onClick={() => onOpenQuote && onOpenQuote(p)}
                className="mono"
                style={{
                  background:'#fff',
                  color:'#1E40AF',
                  padding:'12px 26px',
                  borderRadius:99,
                  fontSize:12,
                  fontWeight:700,
                  textTransform:'uppercase',
                  letterSpacing:'0.08em',
                  cursor:'pointer',
                  border:'none'
                }}
              >
                Request a Free Quote for This Solution →
              </button>
              <button
                onClick={onClose}
                className="mono"
                style={{
                  background:'transparent',
                  border:'1px solid rgba(255,255,255,.4)',
                  color:'#fff',
                  padding:'12px 20px',
                  borderRadius:99,
                  fontSize:11.5,
                  cursor:'pointer'
                }}
              >
                Continue Browsing
              </button>
            </div>
          </div>

        </div>
      </div>
      {lightboxIndex !== null && (
        <LightboxModal
          images={imgs}
          initialIndex={lightboxIndex}
          title={p.title}
          onClose={() => setLightboxIndex(null)}
        />
      )}
    </div>,
    document.body
  );
}

// ─── Auto Device Shot Helper ──────────────────────────────────────────────────
function autoDeviceShot(url, device) {
  if (!url) return '';
  let u = String(url).trim();
  if (u.startsWith('//')) u = 'https:' + u;
  else if (!/^https?:\/\//i.test(u)) u = 'https://' + u;
  return `/api/screenshot?url=${encodeURIComponent(u)}&device=${encodeURIComponent(device)}`;
}

// ─── Unified Responsive Device Showcase Modal ─────────────────────────────────
function ResponsiveDeviceModal({ project: p, initialDevice = 'mobile', scores = {}, onClose }) {
  const [device, setDevice] = useState(initialDevice);
  const [viewMode, setViewMode] = useState('screenshot'); // 'screenshot' | 'live'
  const [shotIndex, setShotIndex] = useState(0);
  const [isFullScroll, setIsFullScroll] = useState(true);
  const [liveReloadKey, setLiveReloadKey] = useState(0);
  const [embedStatus, setEmbedStatus] = useState({ checked: false, ok: true, reason: '' });
  const screenRef = useRef(null);

  const liveUrl = resolveFeatureUrl(p);
  const displayUrl = liveUrl ? liveUrl.replace(/^https?:\/\//, '').replace(/\/$/, '') : '';

  // Lock background body scroll while modal is active
  useEffect(() => {
    const prevOverflow = document.body.style.overflow;
    document.body.style.overflow = 'hidden';
    return () => { document.body.style.overflow = prevOverflow; };
  }, []);

  const DEVICE_CONFIGS = {
    mobile: {
      key: 'mobile',
      label: 'Mobile',
      icon: Smartphone,
      width: 375,
      height: 812,
      viewport: '375 × 812 px',
      range: '320–767px',
      score: scores.mobile || p.metrics?.responsive?.mobile || 98,
      frameMaxW: 380,
      screenH: 560
    },
    tablet: {
      key: 'tablet',
      label: 'Tablet',
      icon: Tablet,
      width: 768,
      height: 1024,
      viewport: '768 × 1024 px',
      range: '768–1023px',
      score: scores.tablet || p.metrics?.responsive?.tablet || 99,
      frameMaxW: 840,
      screenH: 560
    },
    desktop: {
      key: 'desktop',
      label: 'Desktop',
      icon: Monitor,
      width: 1280,
      height: 800,
      viewport: '1280 × 800 px',
      range: '1024px–4K',
      score: scores.desktop || p.metrics?.responsive?.desktop || 100,
      frameMaxW: 1060,
      screenH: 540
    }
  };

  const curDev = DEVICE_CONFIGS[device] || DEVICE_CONFIGS.mobile;

  // Keydown listener for Esc and Arrow keys
  useEffect(() => {
    const onKey = (e) => {
      if (e.key === 'Escape') onClose();
      if (e.key === 'ArrowRight') setShotIndex(i => i + 1);
      if (e.key === 'ArrowLeft') setShotIndex(i => Math.max(0, i - 1));
    };
    window.addEventListener('keydown', onKey);
    return () => window.removeEventListener('keydown', onKey);
  }, [onClose]);

  // Embed check for live URL
  useEffect(() => {
    if (!liveUrl) return;
    let cancelled = false;
    fetch(`/api/embed-check?url=${encodeURIComponent(liveUrl)}`)
      .then(r => r.json())
      .then(j => {
        if (!cancelled) setEmbedStatus({ checked: true, ok: !!j.embeddable, reason: j.reason || '' });
      })
      .catch(() => {
        if (!cancelled) setEmbedStatus({ checked: true, ok: true, reason: '' });
      });
    return () => { cancelled = true; };
  }, [liveUrl]);

  // Reset screenshot index and scroll position when switching devices
  useEffect(() => {
    setShotIndex(0);
    if (screenRef.current) {
      screenRef.current.scrollTop = 0;
    }
  }, [device, liveReloadKey]);

  // Screenshots available for this device
  const shots = useMemo(() => {
    const manual = p.responsiveShots?.[device] || [];
    if (manual.length > 0) return manual;
    if (device === 'desktop' && Array.isArray(p.images) && p.images.length > 0) {
      return [p.images[0]];
    }
    if (liveUrl) {
      const autoShot = autoDeviceShot(liveUrl, device);
      if (autoShot) return [autoShot];
    }
    return p.images?.length ? p.images : (p.image ? [p.image] : []);
  }, [p, device, liveUrl]);

  const activeShot = shots[shotIndex % shots.length] || '';

  return createPortal(
    <div
      style={{
        position: 'fixed',
        top: 0,
        left: 0,
        right: 0,
        bottom: 0,
        width: '100vw',
        height: '100vh',
        zIndex: 99999,
        background: 'rgba(5, 10, 24, 0.88)',
        backdropFilter: 'blur(16px)',
        WebkitBackdropFilter: 'blur(16px)',
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        padding: '16px',
        boxSizing: 'border-box'
      }}
      onClick={onClose}
    >
      <div
        className="anim-fadeUp"
        style={{
          width: '100%',
          maxWidth: device === 'desktop' ? 1160 : (device === 'tablet' ? 940 : 540),
          maxHeight: '92vh',
          background: '#0F172A',
          borderRadius: 22,
          border: '1.5px solid rgba(255, 255, 255, 0.14)',
          boxShadow: '0 30px 90px -10px rgba(0, 0, 0, 0.85), 0 0 0 1px rgba(255,255,255,0.06)',
          display: 'flex',
          flexDirection: 'column',
          overflow: 'hidden',
          color: '#FFFFFF'
        }}
        onClick={e => e.stopPropagation()}
      >
        {/* Modal Top Chrome Header */}
        <div style={{
          padding: '14px 22px',
          background: 'linear-gradient(180deg, #1E293B 0%, #0F172A 100%)',
          borderBottom: '1px solid rgba(255, 255, 255, 0.08)',
          display: 'flex',
          flexWrap: 'wrap',
          alignItems: 'center',
          justifyContent: 'space-between',
          gap: 12
        }}>
          <div style={{ display: 'flex', alignItems: 'center', gap: 12, minWidth: 0 }}>
            <div style={{
              width: 38,
              height: 38,
              borderRadius: 12,
              background: '#1E40AF',
              color: '#93C5FD',
              display: 'flex',
              alignItems: 'center',
              justifyContent: 'center',
              flexShrink: 0,
              boxShadow: '0 4px 14px rgba(30, 64, 175, 0.4)'
            }}>
              <curDev.icon size={20} />
            </div>
            <div style={{ minWidth: 0 }}>
              <div style={{ display: 'flex', alignItems: 'center', gap: 8, flexWrap: 'wrap' }}>
                <span style={{ fontWeight: 700, fontSize: 16, color: '#FFFFFF' }}>
                  {p.title}
                </span>
                <span style={{
                  fontSize: 10.5,
                  padding: '2px 8px',
                  borderRadius: 99,
                  background: 'rgba(59, 130, 246, 0.2)',
                  border: '1px solid rgba(96, 165, 250, 0.4)',
                  color: '#93C5FD',
                  fontFamily: 'Geist Mono, monospace',
                  fontWeight: 700,
                  textTransform: 'uppercase'
                }}>
                  {curDev.label} Preview
                </span>
              </div>
              <div className="mono" style={{ fontSize: 11, color: '#94A3B8', marginTop: 2 }}>
                {curDev.viewport} · Lighthouse Responsive Score: <strong style={{ color: '#34D399' }}>{curDev.score}/100</strong>
              </div>
            </div>
          </div>

          <div style={{ display: 'flex', alignItems: 'center', gap: 10, flexShrink: 0 }}>
            {liveUrl && (
              <a
                href={liveUrl}
                target="_blank"
                rel="noopener noreferrer"
                className="mono"
                style={{
                  display: 'inline-flex',
                  alignItems: 'center',
                  gap: 6,
                  padding: '6px 14px',
                  borderRadius: 99,
                  background: '#2563EB',
                  color: '#FFFFFF',
                  fontSize: 11,
                  fontWeight: 700,
                  textDecoration: 'none',
                  boxShadow: '0 2px 10px rgba(37, 99, 235, 0.4)'
                }}
              >
                <span>Visit Live Site</span>
                <ExternalLink size={12} strokeWidth={2.5} />
              </a>
            )}

            <button
              onClick={onClose}
              aria-label="Close Preview"
              style={{
                width: 32,
                height: 32,
                borderRadius: '50%',
                background: 'rgba(255, 255, 255, 0.08)',
                border: '1px solid rgba(255, 255, 255, 0.15)',
                color: '#E2E8F0',
                cursor: 'pointer',
                display: 'flex',
                alignItems: 'center',
                justifyContent: 'center',
                transition: 'all .15s'
              }}
              onMouseEnter={e => { e.currentTarget.style.background = '#EF4444'; e.currentTarget.style.color = '#fff'; }}
              onMouseLeave={e => { e.currentTarget.style.background = 'rgba(255, 255, 255, 0.08)'; e.currentTarget.style.color = '#E2E8F0'; }}
            >
              <X size={16} strokeWidth={2.4} />
            </button>
          </div>
        </div>

        {/* Device Switcher & Mode Control Bar */}
        <div style={{
          padding: '10px 22px',
          background: '#0B132B',
          borderBottom: '1px solid rgba(255, 255, 255, 0.08)',
          display: 'flex',
          flexWrap: 'wrap',
          alignItems: 'center',
          justifyContent: 'space-between',
          gap: 12
        }}>
          {/* Device Tabs */}
          <div style={{ display: 'flex', alignItems: 'center', gap: 6, background: '#020617', padding: 3, borderRadius: 99, border: '1px solid rgba(255, 255, 255, 0.1)' }}>
            {Object.values(DEVICE_CONFIGS).map(d => {
              const active = device === d.key;
              return (
                <button
                  key={d.key}
                  onClick={() => setDevice(d.key)}
                  className="mono"
                  style={{
                    display: 'inline-flex',
                    alignItems: 'center',
                    gap: 6,
                    padding: '6px 14px',
                    borderRadius: 99,
                    border: 'none',
                    background: active ? '#2563EB' : 'transparent',
                    color: active ? '#FFFFFF' : '#94A3B8',
                    fontSize: 11,
                    fontWeight: active ? 700 : 500,
                    cursor: 'pointer',
                    transition: 'all .15s'
                  }}
                >
                  <d.icon size={13} />
                  <span>{d.label}</span>
                  <span style={{
                    fontSize: 9.5,
                    padding: '1px 5px',
                    borderRadius: 99,
                    background: active ? 'rgba(255, 255, 255, 0.25)' : 'rgba(255, 255, 255, 0.08)',
                    color: active ? '#FFFFFF' : '#CBD5E1'
                  }}>
                    {d.score}
                  </span>
                </button>
              );
            })}
          </div>

          {/* Screenshot vs Live Mode Toggle */}
          <div style={{ display: 'flex', alignItems: 'center', gap: 8 }}>
            <div style={{ display: 'flex', alignItems: 'center', gap: 2, background: '#020617', padding: 3, borderRadius: 99, border: '1px solid rgba(255, 255, 255, 0.1)' }}>
              <button
                onClick={() => setViewMode('screenshot')}
                className="mono"
                style={{
                  display: 'inline-flex',
                  alignItems: 'center',
                  gap: 5,
                  padding: '5px 12px',
                  borderRadius: 99,
                  border: 'none',
                  background: viewMode === 'screenshot' ? '#1E40AF' : 'transparent',
                  color: viewMode === 'screenshot' ? '#FFFFFF' : '#94A3B8',
                  fontSize: 10.5,
                  fontWeight: 600,
                  cursor: 'pointer'
                }}
              >
                📸 Verified Screenshot
              </button>

              {liveUrl && (
                <button
                  onClick={() => setViewMode('live')}
                  className="mono"
                  style={{
                    display: 'inline-flex',
                    alignItems: 'center',
                    gap: 5,
                    padding: '5px 12px',
                    borderRadius: 99,
                    border: 'none',
                    background: viewMode === 'live' ? '#2563EB' : 'transparent',
                    color: viewMode === 'live' ? '#FFFFFF' : '#94A3B8',
                    fontSize: 10.5,
                    fontWeight: 600,
                    cursor: 'pointer'
                  }}
                >
                  🌐 Live Web Preview
                </button>
              )}
            </div>

            {viewMode === 'screenshot' && (
              <button
                onClick={() => setIsFullScroll(!isFullScroll)}
                className="mono"
                title={isFullScroll ? "Click for fitted view" : "Click for full page scrollable"}
                style={{
                  padding: '5px 10px',
                  borderRadius: 99,
                  border: '1px solid rgba(255, 255, 255, 0.12)',
                  background: isFullScroll ? 'rgba(255, 255, 255, 0.1)' : 'transparent',
                  color: '#93C5FD',
                  fontSize: 10.5,
                  cursor: 'pointer'
                }}
              >
                {isFullScroll ? '↕ Full Page Scrollable' : '⛶ Fitted View'}
              </button>
            )}

            {viewMode === 'live' && (
              <button
                onClick={() => setLiveReloadKey(k => k + 1)}
                className="mono"
                title="Reload live iframe"
                style={{
                  padding: '5px 10px',
                  borderRadius: 99,
                  border: '1px solid rgba(255, 255, 255, 0.12)',
                  background: 'transparent',
                  color: '#93C5FD',
                  fontSize: 10.5,
                  cursor: 'pointer'
                }}
              >
                ↻ Reload
              </button>
            )}
          </div>
        </div>

        {/* Device Stage Showcase Area */}
        <div style={{
          flex: 1,
          background: '#0B132B',
          padding: '24px 16px',
          overflowY: 'auto',
          display: 'flex',
          flexDirection: 'column',
          alignItems: 'center',
          justifyContent: 'center',
          minHeight: 460
        }}>
          {/* RENDER DEVICE SPECIFIC CHASSIS */}
          {device === 'mobile' && (
            <div style={{
              width: '100%',
              maxWidth: curDev.frameMaxW,
              background: '#0F172A',
              borderRadius: 44,
              padding: '12px 10px',
              border: '3.5px solid #334155',
              boxShadow: '0 25px 65px -15px rgba(0, 0, 0, 0.8), inset 0 0 0 1.5px rgba(255, 255, 255, 0.15)',
              position: 'relative'
            }}>
              {/* Dynamic Island Speaker / Camera */}
              <div style={{
                width: 96,
                height: 22,
                background: '#020617',
                borderRadius: 99,
                margin: '0 auto 10px',
                display: 'flex',
                alignItems: 'center',
                justifyContent: 'center',
                gap: 7
              }}>
                <span style={{ width: 6, height: 6, borderRadius: '50%', background: '#1E293B' }} />
                <span style={{ width: 4, height: 4, borderRadius: '50%', background: '#334155' }} />
              </div>

              {/* Mobile Screen Glass */}
              <div
                ref={screenRef}
                style={{
                  borderRadius: 30,
                  overflowY: isFullScroll && viewMode === 'screenshot' ? 'auto' : 'hidden',
                  overflowX: 'hidden',
                  background: '#FFFFFF',
                  height: 'min(58vh, 560px)',
                  position: 'relative',
                  boxShadow: 'inset 0 0 0 1px rgba(0, 0, 0, 0.1)',
                  display: 'flex',
                  flexDirection: 'column',
                  alignItems: 'center'
                }}
              >
                {viewMode === 'screenshot' ? (
                  activeShot ? (
                    <img
                      src={activeShot}
                      alt={`${p.title} Mobile Screenshot`}
                      style={{
                        width: '100%',
                        maxWidth: '100%',
                        height: isFullScroll ? 'auto' : '100%',
                        objectFit: 'contain',
                        objectPosition: 'top center',
                        display: 'block'
                      }}
                      onError={e => { e.target.style.opacity = '.3'; }}
                    />
                  ) : (
                    <div style={{ height: '100%', display: 'flex', alignItems: 'center', justifyContent: 'center', color: '#64748B', fontSize: 12 }}>
                      No screenshot available
                    </div>
                  )
                ) : (
                  /* Live Mode */
                  embedStatus.ok ? (
                    <iframe
                      key={`mob-${liveReloadKey}`}
                      src={liveUrl}
                      title={`${p.title} Mobile Live`}
                      loading="lazy"
                      referrerPolicy="no-referrer"
                      sandbox="allow-scripts allow-same-origin allow-forms allow-popups allow-presentation"
                      style={{ width: '100%', height: '100%', border: 'none', display: 'block', background: '#FFFFFF' }}
                    />
                  ) : (
                    <div style={{ height: '100%', display: 'flex', flexDirection: 'column', alignItems: 'center', justifyContent: 'center', padding: 20, textAlign: 'center', background: '#F8FAFC', color: '#0F172A' }}>
                      <Shield size={32} style={{ color: '#2563EB', marginBottom: 10 }} />
                      <div style={{ fontWeight: 700, fontSize: 15, marginBottom: 4 }}>Protected Live Mobile Site</div>
                      <p style={{ fontSize: 11.5, color: '#64748B', lineHeight: 1.45, margin: '0 0 16px' }}>
                        {displayUrl} enforces security headers preventing embedded frames.
                      </p>
                      <a
                        href={liveUrl}
                        target="_blank"
                        rel="noopener noreferrer"
                        className="mono"
                        style={{
                          background: '#2563EB',
                          color: '#FFFFFF',
                          padding: '9px 16px',
                          borderRadius: 99,
                          fontSize: 11,
                          fontWeight: 700,
                          textDecoration: 'none'
                        }}
                      >
                        Launch Mobile View ↗
                      </a>
                    </div>
                  )
                )}
              </div>

              {/* Bottom Home Swipe Bar */}
              <div style={{
                width: 100,
                height: 4,
                background: 'rgba(255, 255, 255, 0.4)',
                borderRadius: 99,
                margin: '10px auto 2px'
              }} />
            </div>
          )}

          {device === 'tablet' && (
            <div style={{
              width: '100%',
              maxWidth: 'min(100%, 820px)',
              background: '#0F172A',
              borderRadius: 28,
              padding: '14px 12px',
              border: '3.5px solid #334155',
              boxShadow: '0 25px 65px -15px rgba(0, 0, 0, 0.8), inset 0 0 0 1.5px rgba(255, 255, 255, 0.15)',
              position: 'relative'
            }}>
              {/* Camera Dot */}
              <div style={{ width: 6, height: 6, borderRadius: '50%', background: '#334155', margin: '0 auto 10px' }} />

              {/* Tablet Screen Glass */}
              <div
                ref={screenRef}
                style={{
                  borderRadius: 18,
                  overflowY: isFullScroll && viewMode === 'screenshot' ? 'auto' : 'hidden',
                  overflowX: 'hidden',
                  background: '#FFFFFF',
                  height: 'min(58vh, 560px)',
                  position: 'relative',
                  display: 'flex',
                  flexDirection: 'column',
                  alignItems: 'center'
                }}
              >
                {viewMode === 'screenshot' ? (
                  activeShot ? (
                    <img
                      src={activeShot}
                      alt={`${p.title} Tablet Screenshot`}
                      style={{
                        width: '100%',
                        maxWidth: '100%',
                        height: isFullScroll ? 'auto' : '100%',
                        objectFit: 'contain',
                        objectPosition: 'top center',
                        display: 'block'
                      }}
                      onError={e => { e.target.style.opacity = '.3'; }}
                    />
                  ) : (
                    <div style={{ height: '100%', display: 'flex', alignItems: 'center', justifyContent: 'center', color: '#64748B', fontSize: 12 }}>
                      No screenshot available
                    </div>
                  )
                ) : (
                  embedStatus.ok ? (
                    <div style={{ width: '100%', height: '100%', overflow: 'hidden', display: 'flex', justifyContent: 'center' }}>
                      <iframe
                        key={`tab-${liveReloadKey}`}
                        src={liveUrl}
                        title={`${p.title} Tablet Live`}
                        loading="lazy"
                        referrerPolicy="no-referrer"
                        sandbox="allow-scripts allow-same-origin allow-forms allow-popups allow-presentation"
                        style={{ width: '100%', height: '100%', minHeight: 480, border: 'none', display: 'block', background: '#FFFFFF' }}
                      />
                    </div>
                  ) : (
                    <div style={{ height: '100%', display: 'flex', flexDirection: 'column', alignItems: 'center', justifyContent: 'center', padding: 24, textAlign: 'center', background: '#F8FAFC', color: '#0F172A' }}>
                      <Shield size={34} style={{ color: '#2563EB', marginBottom: 12 }} />
                      <div style={{ fontWeight: 700, fontSize: 16, marginBottom: 6 }}>Protected Live Tablet Site</div>
                      <p style={{ fontSize: 12, color: '#64748B', lineHeight: 1.5, margin: '0 0 18px' }}>
                        {displayUrl} enforces security headers preventing embedded frames.
                      </p>
                      <a
                        href={liveUrl}
                        target="_blank"
                        rel="noopener noreferrer"
                        className="mono"
                        style={{
                          background: '#2563EB',
                          color: '#FFFFFF',
                          padding: '10px 18px',
                          borderRadius: 99,
                          fontSize: 11.5,
                          fontWeight: 700,
                          textDecoration: 'none'
                        }}
                      >
                        Launch Tablet View ↗
                      </a>
                    </div>
                  )
                )}
              </div>
            </div>
          )}

          {device === 'desktop' && (
            <div style={{
              width: '100%',
              maxWidth: 'min(100%, 1060px)',
              background: '#FFFFFF',
              borderRadius: 16,
              overflow: 'hidden',
              border: '1.5px solid rgba(255, 255, 255, 0.15)',
              boxShadow: '0 25px 70px -15px rgba(0, 0, 0, 0.85)'
            }}>
              {/* Browser Window Chrome */}
              <div style={{
                padding: '9px 16px',
                background: '#F1F5F9',
                borderBottom: '1px solid #CBD5E1',
                display: 'flex',
                alignItems: 'center',
                gap: 12
              }}>
                <div style={{ display: 'flex', gap: 6 }}>
                  <span style={{ width: 10, height: 10, borderRadius: '50%', background: '#EF4444' }} />
                  <span style={{ width: 10, height: 10, borderRadius: '50%', background: '#F59E0B' }} />
                  <span style={{ width: 10, height: 10, borderRadius: '50%', background: '#10B981' }} />
                </div>
                <div style={{
                  flex: 1,
                  background: '#FFFFFF',
                  borderRadius: 6,
                  padding: '4px 12px',
                  fontFamily: 'Geist Mono, monospace',
                  fontSize: 10.5,
                  color: '#334155',
                  border: '1px solid #CBD5E1',
                  display: 'flex',
                  alignItems: 'center',
                  gap: 6
                }}>
                  <Lock size={11} style={{ color: '#059669' }} />
                  <span>https://{displayUrl || 'alpha-ebike.com'}</span>
                </div>
                {liveUrl && (
                  <a
                    href={liveUrl}
                    target="_blank"
                    rel="noopener noreferrer"
                    className="mono"
                    title="Open live site directly"
                    style={{
                      display: 'flex',
                      alignItems: 'center',
                      gap: 4,
                      fontSize: 10.5,
                      color: '#2563EB',
                      textDecoration: 'none',
                      fontWeight: 600
                    }}
                  >
                    <span>Launch</span>
                    <ExternalLink size={10} />
                  </a>
                )}
              </div>

              {/* Desktop Screen Glass */}
              <div
                ref={screenRef}
                style={{
                  height: 'min(58vh, 540px)',
                  overflowY: isFullScroll && viewMode === 'screenshot' ? 'auto' : 'hidden',
                  overflowX: 'hidden',
                  background: '#FFFFFF',
                  position: 'relative'
                }}
              >
                {viewMode === 'screenshot' ? (
                  activeShot ? (
                    <img
                      src={activeShot}
                      alt={`${p.title} Desktop Screenshot`}
                      style={{
                        width: '100%',
                        maxWidth: '100%',
                        height: isFullScroll ? 'auto' : '100%',
                        objectFit: 'contain',
                        objectPosition: 'top center',
                        display: 'block'
                      }}
                      onError={e => { e.target.style.opacity = '.3'; }}
                    />
                  ) : (
                    <div style={{ height: '100%', display: 'flex', alignItems: 'center', justifyContent: 'center', color: '#64748B', fontSize: 12 }}>
                      No screenshot available
                    </div>
                  )
                ) : (
                  embedStatus.ok ? (
                    <iframe
                      key={`desk-${liveReloadKey}`}
                      src={liveUrl}
                      title={`${p.title} Desktop Live`}
                      loading="lazy"
                      referrerPolicy="no-referrer"
                      sandbox="allow-scripts allow-same-origin allow-forms allow-popups allow-presentation"
                      style={{ width: '100%', height: '100%', border: 'none', display: 'block', background: '#FFFFFF' }}
                    />
                  ) : (
                    <div style={{ height: '100%', display: 'flex', flexDirection: 'column', alignItems: 'center', justifyContent: 'center', padding: 32, textAlign: 'center', background: '#F8FAFC', color: '#0F172A' }}>
                      <Shield size={38} style={{ color: '#2563EB', marginBottom: 14 }} />
                      <div style={{ fontWeight: 700, fontSize: 17, marginBottom: 6 }}>Direct Live Preview</div>
                      <p style={{ fontSize: 13, color: '#64748B', maxWidth: 420, lineHeight: 1.5, margin: '0 0 20px' }}>
                        This domain restricts third-party framing for client security. Launch the live interactive site in a dedicated browser tab!
                      </p>
                      <a
                        href={liveUrl}
                        target="_blank"
                        rel="noopener noreferrer"
                        className="mono"
                        style={{
                          background: '#2563EB',
                          color: '#FFFFFF',
                          padding: '11px 22px',
                          borderRadius: 99,
                          fontSize: 12,
                          fontWeight: 700,
                          textDecoration: 'none'
                        }}
                      >
                        Launch Full Desktop Site ↗
                      </a>
                    </div>
                  )
                )}
              </div>
            </div>
          )}

          {/* Multiple Screenshots Selector Thumbnails */}
          {viewMode === 'screenshot' && shots.length > 1 && (
            <div style={{ display: 'flex', gap: 8, marginTop: 18, alignItems: 'center', justifyContent: 'center', flexWrap: 'wrap' }}>
              <span className="mono" style={{ fontSize: 10, color: '#94A3B8', textTransform: 'uppercase', letterSpacing: '0.08em', marginRight: 4 }}>
                Screenshots ({shots.length}):
              </span>
              {shots.map((src, i) => (
                <button
                  key={i}
                  onClick={() => setShotIndex(i)}
                  style={{
                    width: 44,
                    height: 32,
                    borderRadius: 6,
                    overflow: 'hidden',
                    border: i === (shotIndex % shots.length) ? '2px solid #3B82F6' : '1px solid rgba(255,255,255,0.2)',
                    padding: 0,
                    cursor: 'pointer',
                    background: '#0F172A'
                  }}
                >
                  <img src={src} alt="" style={{ width: '100%', height: '100%', objectFit: 'cover' }} />
                </button>
              ))}
            </div>
          )}
        </div>

        {/* Modal Technical Verification Footer */}
        <div style={{
          padding: '12px 24px',
          background: '#0F172A',
          borderTop: '1px solid rgba(255, 255, 255, 0.08)',
          display: 'flex',
          flexWrap: 'wrap',
          alignItems: 'center',
          justifyContent: 'space-between',
          gap: 12
        }}>
          <div style={{ display: 'flex', alignItems: 'center', gap: 16, fontSize: 11, color: '#94A3B8' }}>
            <span style={{ display: 'inline-flex', alignItems: 'center', gap: 5, color: '#34D399', fontWeight: 600 }}>
              <CheckCircle2 size={13} /> Viewport Meta Passed
            </span>
            <span style={{ display: 'inline-flex', alignItems: 'center', gap: 5, color: '#34D399', fontWeight: 600 }}>
              <CheckCircle2 size={13} /> Touch Targets Verified
            </span>
            <span style={{ display: 'inline-flex', alignItems: 'center', gap: 5, color: '#34D399', fontWeight: 600 }}>
              <CheckCircle2 size={13} /> Zero Content Shift
            </span>
          </div>

          <div className="mono" style={{ fontSize: 10.5, color: '#64748B' }}>
            Press <kbd style={{ background: 'rgba(255,255,255,0.1)', padding: '2px 5px', borderRadius: 4, color: '#E2E8F0' }}>Esc</kbd> to close
          </div>
        </div>
      </div>
    </div>,
    document.body
  );
}

// ─── Device Cards (responsive section) ───────────────────────────────────────
function DeviceCards({ m, p }) {
  const [selectedDevice, setSelectedDevice] = useState(null); // 'mobile' | 'tablet' | 'desktop'
  const rs = m.responsive || {};
  const shots = p.responsiveShots || {};
  const projectUrl = resolveFeatureUrl(p);

  const devices = [
    { l:'Mobile',  I:Smartphone, s:rs.mobile||0,  sub:'320–767px',  key:'mobile'  },
    { l:'Tablet',  I:Tablet,     s:rs.tablet||0,  sub:'768–1023px', key:'tablet'  },
    { l:'Desktop', I:Monitor,    s:rs.desktop||0, sub:'1024–4K',    key:'desktop' },
  ];

  return (
    <>
      <div style={{ marginBottom:20 }}>
        <div className="mono" style={{ fontSize:11, textTransform:'uppercase', color:'#3B82F6', marginBottom:12 }}>§ 03 — Responsive Design</div>
        <div className="resp-3col" style={{ gap:8 }}>
          {devices.map(x => {
            const manualShots = shots[x.key] || [];
            const autoShot = projectUrl ? autoDeviceShot(projectUrl, x.key) : '';
            const devShots = manualShots.length > 0 ? manualShots : (autoShot ? [autoShot] : []);
            const hasShots = devShots.length > 0;
            const isAuto = manualShots.length === 0 && !!autoShot;
            return (
              <div key={x.l}
                onClick={() => setSelectedDevice(x.key)}
                style={{ background:'#fff', padding:14, borderRadius:10, border:'1.5px solid #BFDBFE', cursor:'pointer', transition:'all .2s', position:'relative', overflow:'hidden' }}
                onMouseEnter={e => { e.currentTarget.style.borderColor='#2563EB'; e.currentTarget.style.boxShadow='0 6px 20px rgba(37,99,235,.18)'; e.currentTarget.style.transform='translateY(-2px)'; }}
                onMouseLeave={e => { e.currentTarget.style.borderColor='#BFDBFE'; e.currentTarget.style.boxShadow='none'; e.currentTarget.style.transform='none'; }}>

                {/* Score + icon row */}
                <div style={{ display:'flex', justifyContent:'space-between', alignItems:'flex-start', marginBottom:8 }}>
                  <x.I size={20} color="#3B82F6" />
                  <span className="display" style={{ fontSize:26, color:'#1E40AF' }}>{x.s}</span>
                </div>
                <div className="display" style={{ fontSize:16, marginBottom:2 }}>{x.l}</div>
                <div style={{ fontSize:11, color:'#94A3B8', marginBottom:8 }}>{x.sub}</div>
                <div style={{ height:4, background:'#DBEAFE', borderRadius:99, overflow:'hidden', marginBottom: hasShots ? 10 : 0 }}>
                  <div style={{ height:'100%', background:'#1E40AF', borderRadius:99, width:`${x.s}%`, transition:'width 1s ease-out' }} />
                </div>

                {/* Screenshot preview strip */}
                {hasShots && (
                  <div>
                    {isAuto ? (
                      <div style={{ aspectRatio: x.key === 'mobile' ? '9/16' : x.key === 'tablet' ? '3/4' : '16/10', borderRadius:6, overflow:'hidden', background:'#EFF6FF', marginBottom:6, position:'relative' }}>
                        <FadeImg src={devShots[0]} alt={`${x.l} screenshot`} style={{ width:'100%', height:'100%', objectFit:'cover', objectPosition:'top', display:'block' }} onError={e=>{ e.target.style.opacity='.2'; }} />
                      </div>
                    ) : (
                      <div style={{ display:'flex', gap:4, marginBottom:6 }}>
                        {devShots.slice(0,3).map((src,i) => (
                          <div key={i} style={{ flex:1, aspectRatio:'4/3', borderRadius:4, overflow:'hidden', background:'#EFF6FF' }}>
                            <FadeImg src={src} alt="" style={{ width:'100%', height:'100%', objectFit:'cover', objectPosition:'top', display:'block' }} onError={e=>e.target.style.opacity='.2'} />
                          </div>
                        ))}
                      </div>
                    )}
                    <div style={{ display:'flex', alignItems:'center', justifyContent:'center', gap:4 }}>
                      <span style={{ fontSize:10.5, color:'#2563EB', fontFamily:'Geist,sans-serif', fontWeight:600 }}>
                        Open Device Showcase ↗
                      </span>
                    </div>
                  </div>
                )}

                {/* No-shots hint */}
                {!hasShots && (
                  <div className="mono" style={{ fontSize:9, textTransform:'uppercase', color:'#CBD5E1', letterSpacing:'0.08em' }}>Click to view preview</div>
                )}
              </div>
            );
          })}
        </div>
      </div>

      {/* Unified Responsive Device Modal */}
      {selectedDevice && (
        <ResponsiveDeviceModal
          project={p}
          initialDevice={selectedDevice}
          scores={rs}
          onClose={() => setSelectedDevice(null)}
        />
      )}
    </>
  );
}

function ScoreRing({ value, label, size=100 }) {
  const r = size/2-8, c = 2*Math.PI*r, offset = c-(value/100)*c;
  const color = value>=90?'#16A34A':value>=70?'#D97706':'#DC2626';
  return (
    <div style={{ display:'flex', flexDirection:'column', alignItems:'center' }}>
      <div style={{ position:'relative', width:size, height:size }}>
        <svg width={size} height={size} style={{ transform:'rotate(-90deg)' }}>
          <circle cx={size/2} cy={size/2} r={r} stroke='#DBEAFE' strokeWidth="6" fill="none" />
          <circle cx={size/2} cy={size/2} r={r} stroke={color} strokeWidth="6" fill="none" strokeLinecap="round" strokeDasharray={c} strokeDashoffset={offset} className="score-stroke" />
        </svg>
        <div style={{ position:'absolute', inset:0, display:'flex', alignItems:'center', justifyContent:'center' }}>
          <span className="display" style={{ fontSize:24, color }}>{value}</span>
        </div>
      </div>
      <div className="mono" style={{ fontSize:10, textTransform:'uppercase', letterSpacing:'0.1em', color:'#475569', marginTop:6 }}>{label}</div>
    </div>
  );
}

function CompatibilitySection({ project: p }) {
  const compat = p.compatibility || DEFAULT_COMPAT;
  const STATUS = {
    pass: { label:'Pass', color:'#16A34A', bg:'#DCFCE7', dot:'#16A34A' },
    warn: { label:'Warn', color:'#D97706', bg:'#FEF9C3', dot:'#D97706' },
    fail: { label:'Fail', color:'#DC2626', bg:'#FEE2E2', dot:'#DC2626' },
    na:   { label:'N/A',  color:'#94A3B8', bg:'#F1F5F9', dot:'#CBD5E1' },
  };
  const renderChip = (item) => {
    const meta = COMPAT_META[item.name] || {};
    const s = STATUS[item.status] || STATUS.na;
    return (
      <div key={item.name} style={{ display:'flex', alignItems:'center', gap:8, background:'#fff', border:`1.5px solid ${meta.color||'#ccc'}33`, borderRadius:10, padding:'8px 12px' }}>
        <span style={{ display:'flex', alignItems:'center', flexShrink:0 }}>{meta.svg}</span>
        <span style={{ fontSize:12, fontWeight:600, color:'#0F172A', flex:1 }}>{item.name}</span>
        <span style={{ display:'flex', alignItems:'center', gap:4, background:s.bg, borderRadius:99, padding:'2px 8px' }}>
          <span style={{ width:6, height:6, borderRadius:'50%', background:s.dot, flexShrink:0 }} />
          <span className="mono" style={{ fontSize:9, color:s.color, textTransform:'uppercase' }}>{s.label}</span>
        </span>
      </div>
    );
  };
  return (
    <div style={{ marginBottom:24, background:'#F8FAFF', border:'1px solid #DBEAFE', borderRadius:14, padding:20 }}>
      <div className="mono" style={{ fontSize:11, textTransform:'uppercase', color:'#3B82F6', marginBottom:14, letterSpacing:'0.06em' }}>§ Browser & OS Compatibility</div>
      <div className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#64748B', marginBottom:8 }}>Browsers</div>
      <div style={{ display:'grid', gridTemplateColumns:'repeat(auto-fill,minmax(148px,1fr))', gap:8, marginBottom:16 }}>
        {(compat.browsers || []).map(renderChip)}
      </div>
      <div className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#64748B', marginBottom:8 }}>Operating Systems</div>
      <div style={{ display:'grid', gridTemplateColumns:'repeat(auto-fill,minmax(148px,1fr))', gap:8 }}>
        {(compat.os || []).map(renderChip)}
      </div>
    </div>
  );
}

function SecurityAudit({ project: p }) {
  const sec = p.security || DEFAULT_SECURITY;
  const STATUS = {
    pass: { label:'Pass', color:'#16A34A', bg:'#DCFCE7' },
    warn: { label:'Warn', color:'#D97706', bg:'#FEF9C3' },
    fail: { label:'Fail', color:'#DC2626', bg:'#FEE2E2' },
    na:   { label:'N/A',  color:'#94A3B8', bg:'#F1F5F9' },
  };
  const passCount = sec.checks.filter(c => c.status === 'pass').length;
  const total = sec.checks.length;
  const gradeColor = sec.grade?.startsWith('A') ? '#16A34A' : sec.grade?.startsWith('B') ? '#D97706' : '#DC2626';
  return (
    <div style={{ marginBottom:24, background:'#F8FAFF', border:'1px solid #DBEAFE', borderRadius:14, padding:20 }}>
      <div style={{ display:'flex', alignItems:'center', justifyContent:'space-between', marginBottom:14, flexWrap:'wrap', gap:10 }}>
        <div className="mono" style={{ fontSize:11, textTransform:'uppercase', color:'#3B82F6', letterSpacing:'0.06em', display:'flex', alignItems:'center', gap:6 }}>
          <Shield size={13} /> § Security Audit
        </div>
        <div style={{ display:'flex', alignItems:'center', gap:12 }}>
          <div style={{ display:'flex', alignItems:'center', gap:6, background:'#fff', border:'1px solid #DBEAFE', borderRadius:99, padding:'4px 12px' }}>
            <Lock size={11} color="#3B82F6" />
            <span className="mono" style={{ fontSize:10, color:'#475569', textTransform:'uppercase' }}>SSL Labs</span>
            <span className="display" style={{ fontSize:14, color:gradeColor, fontWeight:700 }}>{sec.grade}</span>
          </div>
          <div style={{ display:'flex', alignItems:'center', gap:6, background:'#1E3A8A', color:'#fff', borderRadius:99, padding:'4px 12px' }}>
            <span className="mono" style={{ fontSize:10, color:'#93C5FD', textTransform:'uppercase' }}>Score</span>
            <span className="display" style={{ fontSize:14, fontWeight:700 }}>{sec.score}/100</span>
          </div>
        </div>
      </div>
      <div style={{ background:'#fff', border:'1px solid #DBEAFE', borderRadius:10, padding:'10px 14px', marginBottom:12, display:'flex', alignItems:'center', gap:10 }}>
        <div style={{ flex:1, height:6, background:'#DBEAFE', borderRadius:99, overflow:'hidden' }}>
          <div style={{ height:'100%', width:`${(passCount/total)*100}%`, background:'linear-gradient(90deg,#16A34A,#22C55E)', borderRadius:99, transition:'width 1s ease-out' }} />
        </div>
        <div className="mono" style={{ fontSize:11, color:'#16A34A', fontWeight:600 }}>{passCount}/{total} passed</div>
      </div>
      <div style={{ display:'grid', gridTemplateColumns:'repeat(auto-fill,minmax(220px,1fr))', gap:8 }}>
        {sec.checks.map(c => {
          const s = STATUS[c.status] || STATUS.na;
          return (
            <div key={c.name} style={{ background:'#fff', border:'1px solid #E2E8F0', borderRadius:10, padding:'10px 12px', display:'flex', alignItems:'center', gap:10 }}>
              <span style={{ width:28, height:28, borderRadius:'50%', background:s.bg, display:'flex', alignItems:'center', justifyContent:'center', flexShrink:0 }}>
                <Shield size={13} color={s.color} />
              </span>
              <div style={{ flex:1, minWidth:0 }}>
                <div style={{ fontSize:12, fontWeight:600, color:'#0F172A', whiteSpace:'nowrap', overflow:'hidden', textOverflow:'ellipsis' }}>{c.name}</div>
                {c.detail && <div className="mono" style={{ fontSize:9, color:'#64748B', marginTop:1, whiteSpace:'nowrap', overflow:'hidden', textOverflow:'ellipsis' }}>{c.detail}</div>}
              </div>
              <span style={{ display:'flex', alignItems:'center', gap:4, background:s.bg, borderRadius:99, padding:'2px 8px', flexShrink:0 }}>
                <span style={{ width:6, height:6, borderRadius:'50%', background:s.color, flexShrink:0 }} />
                <span className="mono" style={{ fontSize:9, color:s.color, textTransform:'uppercase', fontWeight:600 }}>{s.label}</span>
              </span>
            </div>
          );
        })}
      </div>
      <div className="mono" style={{ fontSize:9, color:'#94A3B8', marginTop:10, textTransform:'uppercase', letterSpacing:'0.08em' }}>Scanned {sec.scannedOn} · SSL Labs · Mozilla Observatory · OWASP ZAP</div>
    </div>
  );
}

const FEATURE_ICONS = {
  https:'Lock', responsive:'Smartphone', seo:'Search', og:'Eye', schema:'BadgeCheck',
  analytics:'TrendingUp', ecommerce:'ShoppingBag', contact:'Mail', chat:'MessageCircle',
  whatsapp:'Phone', social:'Users', newsletter:'Mail', multilang:'Globe', blog:'Layers',
  search:'Search', cdn:'Zap', cookie:'CheckCircle2', lazyimg:'Eye', fonts:'Sparkles',
  video:'Film', gallery:'Eye', login:'User', pwa:'Rocket', favicon:'Target',
};

const ICON_COMPONENTS = {
  Lock, Smartphone, Search, Eye, BadgeCheck, TrendingUp, ShoppingBag, Mail, MessageCircle,
  Phone, Users, Globe, Layers, Zap, CheckCircle2, Sparkles, Film, User, Rocket, Target,
};

function WebsiteFeatures({ project }) {
  const url = resolveFeatureUrl(project);
  const [state, setState] = useState({ loading: true, features: [], error: '' });

  useEffect(() => {
    if (!url) { setState({ loading: false, features: [], error: 'no url' }); return; }
    let cancelled = false;
    setState({ loading: true, features: [], error: '' });
    fetch(`/api/features?url=${encodeURIComponent(url)}`)
      .then(r => r.json().then(j => ({ ok: r.ok, j })))
      .then(({ ok, j }) => {
        if (cancelled) return;
        if (!ok || j.error) setState({ loading: false, features: [], error: j.error || 'fetch failed' });
        else setState({ loading: false, features: j.features || [], error: '' });
      })
      .catch(e => { if (!cancelled) setState({ loading: false, features: [], error: e.message }); });
    return () => { cancelled = true; };
  }, [url]);

  if (!url) return null;

  return (
    <div style={{ marginBottom:22 }}>
      <div className="mono" style={{ fontSize:11, textTransform:'uppercase', color:'#3B82F6', marginBottom:12 }}>§ Website Features</div>
      <div style={{ background:'#EFF6FF', border:'1px solid #DBEAFE', padding:18, borderRadius:12 }}>
        {state.loading && (
          <div style={{ display:'grid', gridTemplateColumns:'1fr 1fr', gap:10 }}>
            {Array.from({ length: 10 }).map((_, i) => (
              <div key={i} style={{ display:'flex', alignItems:'center', gap:10, background:'#fff', padding:'11px 12px', borderRadius:8, border:'1px solid #DBEAFE', opacity:.55 }}>
                <div style={{ width:30, height:30, borderRadius:8, background:'#DBEAFE' }} />
                <div style={{ flex:1, height:14, background:'#DBEAFE', borderRadius:4 }} />
              </div>
            ))}
          </div>
        )}
        {!state.loading && state.error && (
          <div style={{ fontSize:13, color:'#94A3B8', textAlign:'center', padding:'14px 8px' }}>
            Couldn't auto-scan this site ({state.error}).
          </div>
        )}
        {!state.loading && !state.error && state.features.length === 0 && (
          <div style={{ fontSize:13, color:'#94A3B8', textAlign:'center', padding:'14px 8px' }}>
            No features detected.
          </div>
        )}
        {!state.loading && !state.error && state.features.length > 0 && (
          <div style={{ display:'grid', gridTemplateColumns:'1fr 1fr', gap:10 }}>
            {state.features.map(f => {
              const Icon = ICON_COMPONENTS[FEATURE_ICONS[f.key]] || CheckCircle2;
              return (
                <div key={f.key} style={{ display:'flex', alignItems:'center', gap:11, background:'#fff', padding:'11px 12px', borderRadius:8, border:'1px solid #DBEAFE', transition:'transform .15s, box-shadow .15s' }}
                  onMouseEnter={e => { e.currentTarget.style.transform='translateY(-1px)'; e.currentTarget.style.boxShadow='0 6px 16px rgba(37,99,235,.12)'; }}
                  onMouseLeave={e => { e.currentTarget.style.transform='none'; e.currentTarget.style.boxShadow='none'; }}>
                  <div style={{ width:32, height:32, borderRadius:8, background:'#2563EB', color:'#fff', display:'flex', alignItems:'center', justifyContent:'center', flexShrink:0 }}>
                    <Icon size={15} strokeWidth={2.4} />
                  </div>
                  <div style={{ flex:1, minWidth:0 }}>
                    <div style={{ fontSize:13, fontWeight:700, color:'#0F172A', lineHeight:1.25 }}>{f.label}</div>
                    {f.detail && <div style={{ fontSize:11, color:'#64748B', marginTop:1 }}>{f.detail}</div>}
                  </div>
                  <CheckCircle2 size={14} color="#16A34A" strokeWidth={2.5} style={{ flexShrink:0 }} />
                </div>
              );
            })}
          </div>
        )}
        {!state.loading && state.features.length > 0 && (
          <div className="mono" style={{ fontSize:9, color:'#64748B', marginTop:10, textAlign:'right' }}>
            Auto-detected from {url.replace(/^https?:\/\//,'').replace(/\/$/,'')}
          </div>
        )}
      </div>
    </div>
  );
}

function WebsiteReport({ project: p }) {
  const m = p.metrics || DEFAULT_METRICS;
  return (
    <>
      <div className="resp-2to1" style={{ marginBottom:24, paddingBottom:24, borderBottom:'1px solid #DBEAFE' }}>
        <div>
          <div className="mono" style={{ fontSize:11, textTransform:'uppercase', color:'#3B82F6', marginBottom:8 }}>§ Project Overview</div>
          <p className="display" style={{ fontSize:19, color:'#0F172A', lineHeight:1.5 }}>Built for <span className="display-it">{p.client}</span></p>
          <div style={{ display:'flex', flexWrap:'wrap', gap:6, marginTop:10 }}>
            {p.tags.map(t=><span key={t} className="mono" style={{ fontSize:10, padding:'4px 10px', background:'#1E3A8A', color:'#fff', borderRadius:99, textTransform:'uppercase', letterSpacing:'0.08em' }}>{t}</span>)}
          </div>
        </div>
        <div style={{ background:'#EFF6FF', border:'1px solid #DBEAFE', padding:18, borderRadius:12 }}>
          <div className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#3B82F6', marginBottom:10 }}>Tested Browsers</div>
          <div style={{ display:'flex', flexWrap:'nowrap', gap:6, overflowX:'auto' }}>
            {(p.compatibility?.browsers || DEFAULT_COMPAT.browsers).map(b => {
              const meta = COMPAT_META[b.name] || {};
              const statusColor = b.status === 'pass' ? '#16A34A' : b.status === 'warn' ? '#D97706' : '#DC2626';
              return (
                <div key={b.name} title={b.name} style={{ display:'flex', alignItems:'center', gap:5, background:meta.bg||'#f0f0f0', borderRadius:8, padding:'5px 8px', border:`1px solid ${meta.color||'#ccc'}33` }}>
                  <span style={{ display:'flex', alignItems:'center' }}>{meta.svg}</span>
                  <span style={{ width:6, height:6, borderRadius:'50%', background:statusColor, flexShrink:0 }} />
                </div>
              );
            })}
          </div>
          <div className="mono" style={{ fontSize:9, color:'#64748B', marginTop:8 }}>Lighthouse v11 · Manual QA</div>
        </div>
      </div>
      <div style={{ marginBottom:22 }}>
        <div className="mono" style={{ fontSize:11, textTransform:'uppercase', color:'#3B82F6', marginBottom:12 }}>§ Lighthouse Scores</div>
        <div className="resp-4col" style={{ background:'#EFF6FF', padding:18, borderRadius:12, border:'1px solid #DBEAFE' }}>
          <ScoreRing value={m.performance} label="Performance" />
          <ScoreRing value={m.accessibility} label="Accessibility" />
          <ScoreRing value={m.bestPractices} label="Best Practices" />
          <ScoreRing value={m.seo} label="SEO" />
        </div>
      </div>
      <div className="resp-4col" style={{ gap:8, marginBottom:20 }}>
        {[{k:'FCP',v:m.fcp,d:'First Contentful Paint',I:Zap},{k:'LCP',v:m.lcp,d:'Largest Contentful Paint',I:Eye},{k:'TBT',v:m.tbt,d:'Total Blocking Time',I:Code},{k:'CLS',v:m.cls,d:'Layout Shift',I:Globe}].map(x=>(
          <div key={x.k} style={{ background:'#fff', padding:12, borderRadius:10, border:'1px solid #DBEAFE' }}>
            <div style={{ display:'flex', justifyContent:'space-between', marginBottom:5 }}><span className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#64748B' }}>{x.k}</span><x.I size={11} color="#93C5FD" /></div>
            <div className="display" style={{ fontSize:24, color:'#0F172A' }}>{x.v}</div>
            <div style={{ fontSize:11, color:'#94A3B8', marginTop:2 }}>{x.d}</div>
            <div className="mono" style={{ fontSize:9, color:'#16A34A', marginTop:4 }}>● Good</div>
          </div>
        ))}
      </div>
      <WebsiteFeatures project={p} />
      <DeviceCards m={m} p={p} />
      <CompatibilitySection project={p} />
      <SecurityAudit project={p} />
      <div className="resp-3col" style={{ gap:8, marginBottom:4 }}>
        <div style={{ background:'#1E3A8A', color:'#fff', padding:14, borderRadius:10 }}><div className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#60A5FA', marginBottom:5 }}>Ranking Keywords</div><div className="display" style={{ fontSize:38 }}>{m.keywords}</div></div>
        <div style={{ background:'#fff', padding:14, borderRadius:10, border:'1px solid #DBEAFE' }}><div className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#3B82F6', marginBottom:5 }}>Backlinks</div><div className="display" style={{ fontSize:38, color:'#0F172A' }}>{m.backlinks}</div></div>
        <div style={{ background:'#1E40AF', color:'#fff', padding:14, borderRadius:10 }}><div className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#BFDBFE', marginBottom:5 }}>Organic Traffic</div><div className="display" style={{ fontSize:38 }}>{m.organicTraffic}</div></div>
      </div>
    </>
  );
}

function LogoView({ project: p }) {
  const palette = p.palette || ['#1E40AF','#3B82F6','#EFF6FF','#0F172A','#93C5FD'];
  return (
    <>
      <p className="display" style={{ fontSize:20, color:'#0F172A', marginBottom:20, lineHeight:1.5 }}>Visual identity for <span className="display-it">{p.client}</span></p>
      <div className="resp-3col" style={{ gap:10, marginBottom:18 }}>
        {['Primary Mark','Monogram','Wordmark'].map((label,i)=>(
          <div key={label} style={{ aspectRatio:'1', borderRadius:12, display:'flex', flexDirection:'column', alignItems:'center', justifyContent:'center', position:'relative', overflow:'hidden', border:'1px solid #DBEAFE', background:i===0?palette[0]:i===1?palette[1]:palette[2], color:i===2?palette[3]:'#fff' }}>
            <div className="display" style={{ fontSize:44 }}>{i===1?p.title.charAt(0):p.title.split(' ')[0]}</div>
            <div className="mono" style={{ fontSize:9, textTransform:'uppercase', opacity:.6, position:'absolute', bottom:10 }}>{label}</div>
          </div>
        ))}
      </div>
      <div className="mono" style={{ fontSize:11, textTransform:'uppercase', color:'#3B82F6', marginBottom:8 }}>Colour Palette</div>
      <div style={{ display:'grid', gridTemplateColumns:'repeat(5,1fr)', gap:8 }}>
        {palette.map((c,i)=><div key={i}><div style={{ aspectRatio:'1', borderRadius:10, background:c, border:'1px solid #DBEAFE' }} /><div className="mono" style={{ fontSize:9, color:'#64748B', marginTop:4 }}>{c}</div></div>)}
      </div>
    </>
  );
}

function SeoView({ project: p }) {
  const s = p.seoData || { before:0, after:0, growth:'0%', keywords1:0, keywords3:0, keywords10:0, domainAuthority:0, period:'' };
  return (
    <>
      <div style={{ background:'#1E40AF', color:'#fff', padding:24, borderRadius:12, marginBottom:18 }}>
        <div className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#BFDBFE', marginBottom:5 }}>Headline Result</div>
        <div className="display" style={{ fontSize:'clamp(3.5rem,9vw,6rem)', lineHeight:.9 }}>+{s.growth}</div>
        <div className="mono" style={{ fontSize:11, color:'#BFDBFE', marginTop:6 }}>Organic traffic · {s.period}</div>
      </div>
      <div style={{ display:'grid', gridTemplateColumns:'repeat(3,1fr)', gap:8 }}>
        {[{l:'Top 1',v:s.keywords1,bg:'#1E3A8A',tc:'#fff'},{l:'Top 3',v:s.keywords3,bg:'#3B82F6',tc:'#fff'},{l:'Top 10',v:s.keywords10,bg:'#EFF6FF',tc:'#0F172A'}].map(x=>(
          <div key={x.l} style={{ background:x.bg, color:x.tc, padding:16, borderRadius:10, border:'1px solid #DBEAFE' }}>
            <div className="mono" style={{ fontSize:10, textTransform:'uppercase', opacity:.7, marginBottom:5 }}>{x.l}</div>
            <div className="display" style={{ fontSize:38 }}>{x.v}</div>
          </div>
        ))}
      </div>
    </>
  );
}

function AppView({ project: p }) {
  const a = p.appData || { downloads:'—', rating:0, reviews:'0', platforms:['iOS','Android'], dau:'—' };
  return (
    <>
      <p className="display app-view-intro" style={{ fontSize:20, color:'#0F172A', marginBottom:18 }}>Mobile app for <span className="display-it">{p.client}</span> · {a.platforms.join(' & ')}</p>
      <div className="app-stats-grid">
        <div className="app-stat-card" style={{ background:'#1E3A8A', color:'#fff' }}><div className="mono app-stat-label" style={{ color:'#60A5FA' }}>Downloads</div><div className="display app-stat-value">{a.downloads}</div></div>
        <div className="app-stat-card" style={{ background:'#1E40AF', color:'#fff' }}><div className="mono app-stat-label" style={{ color:'#BFDBFE' }}>Store Rating</div><div className="display app-stat-value">{a.rating}<span className="app-stat-suffix">/5</span></div><div className="app-stat-sub" style={{ color:'#BFDBFE' }}>{a.reviews} reviews</div></div>
        <div className="app-stat-card" style={{ background:'#EFF6FF', border:'1px solid #DBEAFE' }}><div className="mono app-stat-label" style={{ color:'#3B82F6' }}>Daily Active</div><div className="display app-stat-value" style={{ color:'#0F172A' }}>{a.dau}</div></div>
      </div>
    </>
  );
}

// ─── Admin Login ──────────────────────────────────────────────────────────────
function AdminLogin({ onSuccess, onBack }) {
  const [user, setUser] = useState('');
  const [pass, setPass] = useState('');
  const [err, setErr] = useState('');
  const [loading, setLoading] = useState(false);
  const [lockMsg, setLockMsg] = useState('');

  // Refresh lockout countdown each second while locked.
  useEffect(() => {
    const tick = () => {
      const l = readLockout();
      if (l.until && Date.now() < l.until) {
        const secs = Math.ceil((l.until - Date.now()) / 1000);
        const mm = String(Math.floor(secs / 60)).padStart(2, '0');
        const ss = String(secs % 60).padStart(2, '0');
        setLockMsg(`Too many failed attempts. Try again in ${mm}:${ss}.`);
      } else {
        setLockMsg('');
      }
    };
    tick();
    const id = setInterval(tick, 1000);
    return () => clearInterval(id);
  }, []);

  const submit = async (e) => {
    e.preventDefault();
    setErr('');
    const l = readLockout();
    if (l.until && Date.now() < l.until) return;
    setLoading(true);
    try {
      // small delay to blunt brute-force timing
      await new Promise(r => setTimeout(r, 700));
      const hash = await sha256Hex(pass);
      if (user === ADMIN_USER && hash === ADMIN_PASS_HASH) {
        clearLockout();
        onSuccess();
        return;
      }
      const attempts = (l.attempts || 0) + 1;
      if (attempts >= MAX_ATTEMPTS) {
        writeLockout({ attempts, until: Date.now() + LOCKOUT_MS });
        setErr('Too many failed attempts. Account locked temporarily.');
      } else {
        writeLockout({ attempts, until: 0 });
        setErr(`Invalid credentials. ${MAX_ATTEMPTS - attempts} attempt(s) remaining.`);
      }
    } catch {
      setErr('Authentication error. Please try again.');
    } finally {
      setLoading(false);
    }
  };
  const locked = !!lockMsg;
  return (
    <div style={{ minHeight:'100vh', background:'linear-gradient(135deg,#0F1D3E,#1E3A8A,#0F1D3E)', display:'flex', alignItems:'center', justifyContent:'center', padding:20, position:'relative', overflow:'hidden' }}>
      <div className="blob anim-float" style={{ width:500, height:500, background:'#3B82F6', top:-200, right:-100 }} />
      <div className="blob anim-floatAlt" style={{ width:400, height:400, background:'#60A5FA', bottom:-150, left:-60 }} />
      <div className="anim-fadeUp" style={{ width:'100%', maxWidth:400, background:'rgba(255,255,255,.97)', borderRadius:22, padding:'38px 34px', boxShadow:'0 32px 80px rgba(0,0,0,.35)', position:'relative', zIndex:1 }}>
        <div style={{ textAlign:'center', marginBottom:26 }}>
          <div style={{ width:54, height:54, background:'linear-gradient(135deg,#1E40AF,#3B82F6)', borderRadius:14, display:'flex', alignItems:'center', justifyContent:'center', margin:'0 auto 14px', animation:'pulseRing 2s ease-in-out infinite' }}><Shield size={24} color="#fff" /></div>
          <h1 className="display" style={{ fontSize:30, color:'#0F172A', marginBottom:4 }}>Admin Login</h1>
          <p style={{ fontSize:13, color:'#64748B' }}>Techpenta CMS · Secure Access</p>
        </div>
        <form onSubmit={submit}>
          <div style={{ marginBottom:12 }}>
            <label className="mono" style={{ display:'flex', alignItems:'center', gap:5, fontSize:11, textTransform:'uppercase', letterSpacing:'0.1em', color:'#475569', marginBottom:5 }}><User size={11} /> Username</label>
            <input className="inp" value={user} onChange={e=>setUser(e.target.value)} placeholder="admin" autoComplete="username" disabled={locked} maxLength={64} required />
          </div>
          <div style={{ marginBottom:18 }}>
            <label className="mono" style={{ display:'flex', alignItems:'center', gap:5, fontSize:11, textTransform:'uppercase', letterSpacing:'0.1em', color:'#475569', marginBottom:5 }}><Lock size={11} /> Password</label>
            <input className="inp" type="password" value={pass} onChange={e=>setPass(e.target.value)} placeholder="••••••••••••" autoComplete="current-password" disabled={locked} maxLength={128} required />
          </div>
          {lockMsg && <div style={{ background:'#FEF3C7', color:'#92400E', padding:'10px 12px', borderRadius:8, fontSize:12, marginBottom:12, border:'1px solid #FDE68A' }}>{lockMsg}</div>}
          {err && !lockMsg && <div style={{ background:'#FEF2F2', color:'#DC2626', padding:'10px 12px', borderRadius:8, fontSize:12, marginBottom:12, border:'1px solid #FECACA' }}>{err}</div>}
          <button type="submit" className="btn-primary" disabled={loading || locked} style={{ width:'100%', padding:'13px', borderRadius:12, fontSize:14, fontFamily:'Geist,sans-serif', fontWeight:600 }}>
            {loading ? 'Authenticating…' : locked ? 'Locked' : 'Sign In →'}
          </button>
        </form>
        <button onClick={onBack} style={{ display:'block', margin:'14px auto 0', background:'none', border:'none', color:'#3B82F6', fontSize:13, cursor:'pointer', fontFamily:'Geist,sans-serif' }}>← Back to Portfolio</button>
      </div>
    </div>
  );
}

// ─── Admin Panel ──────────────────────────────────────────────────────────────
const SECTIONS = [
  {id:'hero',label:'Hero Section',icon:'🏠'},{id:'marquee',label:'Marquee',icon:'📜'},
  {id:'projects',label:'Projects',icon:'📁'},{id:'services',label:'Services',icon:'⚙️'},
  {id:'techstack',label:'Tech Stack',icon:'💻'},{id:'industries',label:'Industries',icon:'🏭'},
  {id:'support',label:'Support',icon:'🛡️'},{id:'contact',label:'Contact',icon:'📬'},
];

function AdminPanel({ data, onSave, onLogout }) {
  const [active, setActive] = useState('hero');
  const [local, setLocal] = useState(() => JSON.parse(JSON.stringify(data)));
  const [dirty, setDirty] = useState(false);

  const update = useCallback((path, value) => {
    setLocal(prev => {
      const next = JSON.parse(JSON.stringify(prev));
      const keys = path.split('.');
      let obj = next;
      for (let i = 0; i < keys.length - 1; i++) obj = obj[keys[i].match(/^\d+$/) ? parseInt(keys[i]) : keys[i]];
      const last = keys[keys.length-1];
      obj[last.match(/^\d+$/) ? parseInt(last) : last] = value;
      return next;
    });
    setDirty(true);
  }, []);

  return (
    <div style={{ display:'flex', minHeight:'100vh', background:'#F0F7FF', fontFamily:'Geist,sans-serif' }}>
      <aside style={{ width:230, background:'#0F1D3E', display:'flex', flexDirection:'column', flexShrink:0, position:'sticky', top:0, height:'100vh', overflowY:'auto' }}>
        <div style={{ padding:'22px 18px 14px', borderBottom:'1px solid rgba(255,255,255,.07)' }}>
          <div style={{ display:'flex', alignItems:'center', gap:10 }}>
            <div style={{ width:34, height:34, background:'linear-gradient(135deg,#1E40AF,#3B82F6)', borderRadius:10, display:'flex', alignItems:'center', justifyContent:'center', flexShrink:0 }}><Shield size={16} color="#fff" /></div>
            <div><div style={{ color:'#fff', fontSize:13, fontWeight:600 }}>Techpenta CMS</div><div className="mono" style={{ fontSize:10, color:'#60A5FA', textTransform:'uppercase', letterSpacing:'0.1em' }}>Admin</div></div>
          </div>
        </div>
        <nav style={{ flex:1, padding:'10px 8px' }}>
          {SECTIONS.map(s => (
            <button key={s.id} onClick={() => setActive(s.id)}
              style={{ width:'100%', display:'flex', alignItems:'center', gap:9, padding:'9px 12px', borderRadius:9, border:'none', cursor:'pointer', marginBottom:2, background:active===s.id?'rgba(59,130,246,.22)':'transparent', color:active===s.id?'#60A5FA':'#93C5FD', textAlign:'left', fontSize:13, transition:'all .15s', borderLeft:active===s.id?'3px solid #3B82F6':'3px solid transparent' }}>
              <span style={{ fontSize:15 }}>{s.icon}</span> {s.label}
            </button>
          ))}
        </nav>
        <div style={{ padding:'10px 8px', borderTop:'1px solid rgba(255,255,255,.07)' }}>
          <button onClick={() => { onSave(local); setDirty(false); }} disabled={!dirty}
            style={{ width:'100%', padding:'9px', borderRadius:9, border:'none', cursor:dirty?'pointer':'not-allowed', background:dirty?'#1E40AF':'rgba(255,255,255,.07)', color:dirty?'#fff':'#475569', fontSize:13, fontWeight:600, marginBottom:5, display:'flex', alignItems:'center', justifyContent:'center', gap:6, transition:'all .2s' }}>
            <Save size={13} /> {dirty?'Save Changes':'No Changes'}
          </button>
          <button onClick={onLogout} style={{ width:'100%', padding:'9px', borderRadius:9, border:'1px solid rgba(255,255,255,.1)', cursor:'pointer', background:'transparent', color:'#94A3B8', fontSize:13, display:'flex', alignItems:'center', justifyContent:'center', gap:6 }}>
            <LogOut size={13} /> Logout
          </button>
        </div>
      </aside>

      <main style={{ flex:1, padding:'30px 32px', overflowY:'auto' }}>
        <div className="anim-fadeIn" key={active}>
          {active==='hero'       && <HeroEditor data={local} update={update} setLocal={setLocal} setDirty={setDirty} />}
          {active==='marquee'    && <ListEditor title="Marquee Text" subtitle="Items in the scrolling strip." items={local.marquee} onChange={v=>{setLocal(p=>({...p,marquee:v}));setDirty(true);}} />}
          {active==='projects'   && <ProjectsEditor data={local} setLocal={setLocal} setDirty={setDirty} />}
          {active==='services'   && <ServicesEditor data={local} setLocal={setLocal} setDirty={setDirty} />}
          {active==='techstack'  && <ListEditor title="Tech Stack" subtitle="Technology tags shown in the services section." items={local.techStack} onChange={v=>{setLocal(p=>({...p,techStack:v}));setDirty(true);}} />}
          {active==='industries' && <ListEditor title="Industries" subtitle="Sectors in the industries grid." items={local.industries} onChange={v=>{setLocal(p=>({...p,industries:v}));setDirty(true);}} />}
          {active==='support'    && <SupportEditor data={local} update={update} />}
          {active==='contact'    && <ContactEditor data={local} update={update} setLocal={setLocal} setDirty={setDirty} />}
        </div>
      </main>
    </div>
  );
}

function ACard({ title, children }) {
  return (
    <div style={{ background:'#fff', borderRadius:14, border:'1px solid #DBEAFE', padding:24, marginBottom:18, boxShadow:'0 2px 10px rgba(30,64,175,.05)' }}>
      <h3 style={{ fontSize:16, fontWeight:600, color:'#0F172A', marginBottom:18, paddingBottom:12, borderBottom:'1px solid #F0F7FF' }}>{title}</h3>
      {children}
    </div>
  );
}
function Field({ label, children }) {
  return (
    <div style={{ marginBottom:14 }}>
      <label className="mono" style={{ display:'block', fontSize:11, textTransform:'uppercase', letterSpacing:'0.1em', color:'#475569', marginBottom:5 }}>{label}</label>
      {children}
    </div>
  );
}
function SectionHead({ title, subtitle }) {
  return (
    <div style={{ marginBottom:22 }}>
      <h2 style={{ fontSize:24, fontWeight:700, color:'#0F172A', marginBottom:4 }}>{title}</h2>
      {subtitle && <p style={{ color:'#64748B', fontSize:14 }}>{subtitle}</p>}
    </div>
  );
}

function HeroEditor({ data, update, setLocal, setDirty }) {
  const h = data.hero;
  const bullets = h.bullets || [];

  const addBullet = () => {
    setLocal(p => { const n=JSON.parse(JSON.stringify(p)); n.hero.bullets=[...(n.hero.bullets||[]),'New bullet point']; return n; });
    setDirty(true);
  };
  const editBullet = (i,v) => {
    setLocal(p => { const n=JSON.parse(JSON.stringify(p)); n.hero.bullets[i]=v; return n; });
    setDirty(true);
  };
  const removeBullet = (i) => {
    setLocal(p => { const n=JSON.parse(JSON.stringify(p)); n.hero.bullets.splice(i,1); return n; });
    setDirty(true);
  };

  return (
    <>
      <SectionHead title="Hero / Banner Section" subtitle="2-column banner — left: text & CTA, right: intro video." />

      <ACard title="Badge & Heading">
        <Field label="Badge Pill Text">
          <input className="inp" value={h.badge||''} onChange={e=>update('hero.badge',e.target.value)} placeholder="Kolkata-based Digital Agency · Est. 2010" />
        </Field>
        <Field label="Heading — Main (dark text)">
          <input className="inp" value={h.headingMain||''} onChange={e=>update('hero.headingMain',e.target.value)} placeholder="Build a Powerful Online Presence with" />
        </Field>
        <Field label="Heading — Accent (blue text)">
          <input className="inp" value={h.headingAccent||''} onChange={e=>update('hero.headingAccent',e.target.value)} placeholder="Techpenta e-Solutions Pvt. Ltd." />
        </Field>
        <Field label="Subheading (below heading)">
          <input className="inp" value={h.subheading||''} onChange={e=>update('hero.subheading',e.target.value)} />
        </Field>
      </ACard>

      <ACard title="Bullet Points">
        {bullets.map((b,i) => (
          <div key={i} style={{ display:'flex', gap:7, marginBottom:8 }}>
            <span style={{ marginTop:9, color:'#2563EB', fontSize:10 }}>●</span>
            <input className="inp" value={b} onChange={e=>editBullet(i,e.target.value)} style={{ flex:1 }} />
            <button onClick={()=>removeBullet(i)} style={{ padding:'8px', background:'#FEF2F2', color:'#DC2626', border:'1px solid #FECACA', borderRadius:7, cursor:'pointer', flexShrink:0 }}><Trash2 size={13}/></button>
          </div>
        ))}
        <button onClick={addBullet} style={{ display:'flex', alignItems:'center', gap:5, padding:'7px 14px', background:'#EFF6FF', color:'#1E40AF', border:'1px solid #BFDBFE', borderRadius:8, cursor:'pointer', fontSize:13, marginTop:4 }}><Plus size={13}/> Add Bullet</button>
      </ACard>

      <ACard title="CTA Button">
        <div style={{ display:'grid', gridTemplateColumns:'1fr 1fr', gap:12 }}>
          <Field label="Button Text"><input className="inp" value={h.ctaText||''} onChange={e=>update('hero.ctaText',e.target.value)} placeholder="Get a Free Quote" /></Field>
          <Field label="Button Link"><input className="inp" value={h.ctaLink||''} onChange={e=>update('hero.ctaLink',e.target.value)} placeholder="#contact" /></Field>
        </div>
        <Field label="Disclaimer (below button)">
          <input className="inp" value={h.disclaimer||''} onChange={e=>update('hero.disclaimer',e.target.value)} placeholder="Free consultation. No contracts." />
        </Field>
      </ACard>

      <ACard title="Intro Video (right column)">
        <Field label="Video Quote (shown above the player)">
          <textarea className="inp" rows={2} value={h.videoQuote||''} onChange={e=>update('hero.videoQuote',e.target.value)} style={{ resize:'vertical' }} />
        </Field>
        <Field label="Video URL">
          <input className="inp" value={h.videoUrl||''} onChange={e=>update('hero.videoUrl',e.target.value)} placeholder="YouTube / Vimeo URL or direct .mp4 link" />
          <div style={{ fontSize:12, color:'#94A3B8', marginTop:6 }}>
            Supports: YouTube (youtube.com/watch?v=… or youtu.be/…), Vimeo, or a direct .mp4/.webm URL.
          </div>
        </Field>
        {h.videoUrl && parseVideo(h.videoUrl) && (
          <div style={{ marginTop:10, padding:10, background:'#EFF6FF', borderRadius:8, fontSize:12, color:'#3B82F6', border:'1px solid #BFDBFE' }}>
            ✓ Valid video URL detected — type: <strong>{parseVideo(h.videoUrl).type}</strong>
          </div>
        )}
        <Field label="Video Thumbnail / Poster (shown before play)">
          <input className="inp" value={h.videoPoster||''} onChange={e=>update('hero.videoPoster',e.target.value)} placeholder="/my-thumb.jpg  or  https://…" />
          <div style={{ fontSize:12, color:'#94A3B8', marginTop:6 }}>
            Optional. Leave empty to show the first frame of the video.
          </div>
          {h.videoPoster && (
            <img src={h.videoPoster} alt="poster preview" style={{ marginTop:10, width:'100%', maxWidth:280, aspectRatio:'16/9', objectFit:'cover', borderRadius:8, border:'1px solid #BFDBFE' }} />
          )}
        </Field>
      </ACard>

      <ACard title="Logo">
        <Field label="Logo Image URL"><input className="inp" value={data.logo||''} onChange={e=>update('logo',e.target.value)} /></Field>
        {data.logo && <img src={data.logo} alt="preview" style={{ height:38, marginTop:8, objectFit:'contain' }} />}
      </ACard>
    </>
  );
}

function ListEditor({ title, subtitle, items, onChange }) {
  const [newVal, setNewVal] = useState('');
  const add = () => { if(!newVal.trim()) return; onChange([...items, newVal.trim()]); setNewVal(''); };
  const remove = i => onChange(items.filter((_,idx)=>idx!==i));
  const edit = (i,v) => { const a=[...items]; a[i]=v; onChange(a); };
  return (
    <>
      <SectionHead title={title} subtitle={subtitle} />
      <ACard title="Items">
        <div style={{ display:'grid', gridTemplateColumns:'1fr 1fr', gap:8, marginBottom:12 }}>
          {items.map((item,i) => (
            <div key={i} style={{ display:'flex', gap:6 }}>
              <input className="inp" value={item} onChange={e=>edit(i,e.target.value)} style={{ flex:1 }} />
              <button onClick={()=>remove(i)} style={{ padding:'8px', background:'#FEF2F2', color:'#DC2626', border:'1px solid #FECACA', borderRadius:7, cursor:'pointer' }}><Trash2 size={13} /></button>
            </div>
          ))}
        </div>
        <div style={{ display:'flex', gap:8 }}>
          <input className="inp" value={newVal} onChange={e=>setNewVal(e.target.value)} placeholder="New item…" onKeyDown={e=>e.key==='Enter'&&add()} style={{ flex:1 }} />
          <button onClick={add} className="btn-primary" style={{ padding:'8px 16px', borderRadius:8, fontSize:13, display:'flex', alignItems:'center', gap:5, whiteSpace:'nowrap' }}><Plus size={13} /> Add</button>
        </div>
      </ACard>
    </>
  );
}

function ServicesEditor({ data, setLocal, setDirty }) {
  const add = () => { setLocal(p=>{const n=JSON.parse(JSON.stringify(p));n.services.push({t:'New Service',d:'Description.'});return n;}); setDirty(true); };
  const remove = i => { setLocal(p=>{const n=JSON.parse(JSON.stringify(p));n.services.splice(i,1);return n;}); setDirty(true); };
  const edit = (i,k,v) => { setLocal(p=>{const n=JSON.parse(JSON.stringify(p));n.services[i][k]=v;return n;}); setDirty(true); };
  return (
    <>
      <SectionHead title="Services" />
      <ACard title="Service List">
        {data.services.map((s,i)=>(
          <div key={i} style={{ padding:14, background:'#F8FAFC', borderRadius:9, marginBottom:10, border:'1px solid #E2E8F0' }}>
            <div style={{ display:'flex', justifyContent:'space-between', marginBottom:8 }}>
              <span style={{ fontSize:12, fontWeight:600, color:'#64748B' }}>Service {i+1}</span>
              <button onClick={()=>remove(i)} style={{ background:'none', border:'none', cursor:'pointer', color:'#DC2626' }}><Trash2 size={13} /></button>
            </div>
            <Field label="Title"><input className="inp" value={s.t} onChange={e=>edit(i,'t',e.target.value)} /></Field>
            <Field label="Description"><textarea className="inp" rows={2} value={s.d} onChange={e=>edit(i,'d',e.target.value)} style={{ resize:'vertical' }} /></Field>
          </div>
        ))}
        <button onClick={add} style={{ display:'flex', alignItems:'center', gap:6, padding:'8px 14px', background:'#EFF6FF', color:'#1E40AF', border:'1px solid #BFDBFE', borderRadius:8, cursor:'pointer', fontSize:13 }}><Plus size={13}/> Add Service</button>
      </ACard>
    </>
  );
}

function SupportEditor({ data, update }) {
  return (
    <>
      <SectionHead title="Support Promise" />
      <ACard title="Details">
        <Field label="Days"><input className="inp" value={data.support?.days||''} onChange={e=>update('support.days',e.target.value)} /></Field>
        <Field label="Description"><textarea className="inp" rows={3} value={data.support?.desc||''} onChange={e=>update('support.desc',e.target.value)} style={{ resize:'vertical' }} /></Field>
      </ACard>
    </>
  );
}

function ContactEditor({ data, update, setLocal, setDirty }) {
  const c = data.contact || {};
  const editPhone = (i,v) => { setLocal(p=>{const n=JSON.parse(JSON.stringify(p));n.contact.phones[i]=v;return n;}); setDirty(true); };
  const addPhone = () => { setLocal(p=>{const n=JSON.parse(JSON.stringify(p));n.contact.phones.push('');return n;}); setDirty(true); };
  const removePhone = i => { setLocal(p=>{const n=JSON.parse(JSON.stringify(p));n.contact.phones.splice(i,1);return n;}); setDirty(true); };
  return (
    <>
      <SectionHead title="Contact Info" />
      <ACard title="Details">
        <Field label="Email"><input className="inp" type="email" value={c.email||''} onChange={e=>update('contact.email',e.target.value)} /></Field>
        <Field label="Phone Numbers">
          {(c.phones||[]).map((p,i)=>(
            <div key={i} style={{ display:'flex', gap:7, marginBottom:7 }}>
              <input className="inp" value={p} onChange={e=>editPhone(i,e.target.value)} />
              <button onClick={()=>removePhone(i)} style={{ padding:'8px', background:'#FEF2F2', color:'#DC2626', border:'1px solid #FECACA', borderRadius:7, cursor:'pointer' }}><Trash2 size={13}/></button>
            </div>
          ))}
          <button onClick={addPhone} style={{ display:'flex', alignItems:'center', gap:5, padding:'7px 12px', background:'#EFF6FF', color:'#1E40AF', border:'1px solid #BFDBFE', borderRadius:7, cursor:'pointer', fontSize:13 }}><Plus size={12}/> Add Phone</button>
        </Field>
        <Field label="Address"><textarea className="inp" rows={4} value={c.address||''} onChange={e=>update('contact.address',e.target.value)} style={{ resize:'vertical' }} /></Field>
      </ACard>
    </>
  );
}

// ─── Image upload helpers ─────────────────────────────────────────────────────
// Uploads are sent to /api/upload, which writes a real .jpg under public/projects/
// and returns the served path. We downscale + re-encode to JPEG client-side first
// to keep uploads small.
function fileToDataUrl(file) {
  return new Promise((resolve, reject) => {
    const r = new FileReader();
    r.onload = () => resolve(r.result);
    r.onerror = () => reject(new Error('read failed'));
    r.readAsDataURL(file);
  });
}

function dataUrlToBlob(dataUrl) {
  const [head, b64] = dataUrl.split(',');
  const mime = /data:([^;]+)/.exec(head)?.[1] || 'image/jpeg';
  const bin = atob(b64);
  const arr = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) arr[i] = bin.charCodeAt(i);
  return new Blob([arr], { type: mime });
}

function downscaleToJpegBlob(dataUrl, maxDim = 1600, quality = 0.82) {
  return new Promise((resolve, reject) => {
    const img = new Image();
    img.onload = () => {
      const scale = Math.min(1, maxDim / Math.max(img.width, img.height));
      const w = Math.max(1, Math.round(img.width * scale));
      const h = Math.max(1, Math.round(img.height * scale));
      const canvas = document.createElement('canvas');
      canvas.width = w; canvas.height = h;
      const ctx = canvas.getContext('2d');
      ctx.drawImage(img, 0, 0, w, h);
      try {
        const jpegDataUrl = canvas.toDataURL('image/jpeg', quality);
        resolve(dataUrlToBlob(jpegDataUrl));
      } catch (e) { reject(e); }
    };
    img.onerror = () => reject(new Error('decode failed'));
    img.src = dataUrl;
  });
}

async function uploadImageFile(file) {
  // For webp/gif/svg/avif, preserve the original format. For jpeg/png inputs,
  // downscale + re-encode to JPEG via canvas to keep uploads small. If the
  // browser can't decode the source, fall back to uploading the original bytes.
  const srcType = (file.type || '').toLowerCase();
  const preserveFormats = ['image/webp', 'image/gif', 'image/svg+xml', 'image/avif'];
  let blob, contentType;
  if (preserveFormats.includes(srcType)) {
    blob = file;
    contentType = srcType;
  } else {
    try {
      const raw = await fileToDataUrl(file);
      blob = await downscaleToJpegBlob(raw);
      contentType = 'image/jpeg';
    } catch (e) {
      console.warn('JPEG re-encode failed, uploading original bytes:', e);
      blob = file;
      contentType = file.type || 'application/octet-stream';
    }
  }
  const res = await fetch('/api/upload', {
    method: 'POST',
    headers: { 'Content-Type': contentType },
    body: blob,
  });
  if (!res.ok) {
    throw new Error(`Server ${res.status}: ${res.statusText || 'upload failed'}`);
  }
  const ctype = res.headers.get('content-type') || '';
  if (!ctype.includes('application/json')) {
    throw new Error('Upload endpoint missing — /api/upload did not return JSON. Restart the dev server.');
  }
  const { url, error } = await res.json();
  if (error) throw new Error(error);
  if (!url) throw new Error('No URL returned from server');
  return url;
}

async function uploadVideoFile(file) {
  const contentType = file.type || 'video/mp4';
  const res = await fetch('/api/upload', {
    method: 'POST',
    headers: { 'Content-Type': contentType },
    body: file,
  });
  if (!res.ok) throw new Error(`Server ${res.status}: ${res.statusText || 'upload failed'}`);
  const ctype = res.headers.get('content-type') || '';
  if (!ctype.includes('application/json')) throw new Error('Upload endpoint missing — /api/upload did not return JSON.');
  const { url, error } = await res.json();
  if (error) throw new Error(error);
  if (!url) throw new Error('No URL returned from server');
  return url;
}

function TagsInput({ value, onChange }) {
  const [text, setText] = useState(() => (value || []).join(', '));
  const lastCommittedRef = useRef((value || []).join(', '));

  useEffect(() => {
    const joined = (value || []).join(', ');
    if (joined !== lastCommittedRef.current) {
      setText(joined);
      lastCommittedRef.current = joined;
    }
  }, [value]);

  const commit = () => {
    const arr = text.split(',').map(t => t.trim()).filter(Boolean);
    const joined = arr.join(', ');
    lastCommittedRef.current = joined;
    setText(joined);
    onChange(arr);
  };

  return (
    <input className="inp"
      value={text}
      onChange={e => setText(e.target.value)}
      onBlur={commit}
      onKeyDown={e => { if (e.key === 'Enter') { e.preventDefault(); commit(); e.currentTarget.blur(); } }}
      placeholder="WordPress, PHP, Responsive"
    />
  );
}

function VideoInput({ value, onChange }) {
  const fileRef = useRef(null);
  const [busy, setBusy] = useState(false);
  const [err, setErr] = useState('');

  const pickFile = async (file) => {
    if (!file) return;
    if (!file.type.startsWith('video/')) { setErr('Please select a video file (mp4, webm, mov).'); return; }
    if (file.size > 200 * 1024 * 1024) { setErr('Video is larger than 200 MB.'); return; }
    setErr(''); setBusy(true);
    try {
      const url = await uploadVideoFile(file);
      onChange(url);
    } catch (e) {
      console.error('Video upload failed:', e);
      setErr(e?.message || 'Upload failed.');
    } finally {
      setBusy(false);
      if (fileRef.current) fileRef.current.value = '';
    }
  };

  return (
    <div style={{ display:'flex', flexDirection:'column', gap:6 }}>
      <div style={{ display:'flex', gap:6, alignItems:'center' }}>
        <button type="button" onClick={()=>fileRef.current?.click()} disabled={busy}
          style={{ display:'flex', alignItems:'center', gap:5, padding:'8px 14px', background:'#EFF6FF', color:'#1E40AF', border:'1px solid #BFDBFE', borderRadius:7, cursor:busy?'wait':'pointer', fontSize:12, whiteSpace:'nowrap', flexShrink:0, fontWeight:500 }}>
          <Upload size={13}/> {busy ? 'Uploading video…' : (value ? 'Replace Video' : 'Upload Video (mp4)')}
        </button>
        <input ref={fileRef} type="file" accept="video/mp4,video/webm,video/ogg,video/quicktime,video/x-matroska" onChange={e=>pickFile(e.target.files?.[0])} style={{ display:'none' }} />
        <input className="inp" value={value || ''} onChange={e=>onChange(e.target.value)}
          placeholder="or paste YouTube / Vimeo / direct .mp4 URL"
          style={{ flex:1, minWidth:0, fontSize:12 }} />
        {value && (
          <button type="button" onClick={()=>onChange('')} title="Clear video"
            style={{ padding:'6px 8px', background:'#FEF2F2', color:'#DC2626', border:'1px solid #FECACA', borderRadius:6, cursor:'pointer', flexShrink:0 }}>
            <X size={12}/>
          </button>
        )}
      </div>
      {err && <div style={{ fontSize:11, color:'#DC2626' }}>⚠ {err}</div>}
    </div>
  );
}

function ImageInput({ value, onChange, size = 'md' }) {
  const fileRef = useRef(null);
  const [busy, setBusy] = useState(false);
  const [err, setErr] = useState('');
  const [broken, setBroken] = useState(false);
  const thumb = size === 'sm' ? { w:32, h:22, r:3 } : { w:40, h:28, r:5 };
  const btnPad = size === 'sm' ? '5px 8px' : '6px 10px';
  const fontSize = size === 'sm' ? 11 : 12;

  useEffect(() => { setBroken(false); setErr(''); }, [value]);

  const pickFile = async (file) => {
    if (!file) return;
    if (!file.type.startsWith('image/')) { setErr('Please select an image file.'); return; }
    setErr(''); setBusy(true);
    try {
      const url = await uploadImageFile(file);
      onChange(url);
    } catch (e) {
      console.error('Upload failed:', e);
      setErr(e?.message || 'Upload failed.');
    } finally {
      setBusy(false);
      if (fileRef.current) fileRef.current.value = '';
    }
  };

  return (
    <div style={{ flex:1, minWidth:0, display:'flex', flexDirection:'column', gap:3 }}>
      <div style={{ display:'flex', gap:6, alignItems:'center' }}>
        {value && <img src={value} alt="" style={{ width:thumb.w, height:thumb.h, objectFit:'cover', borderRadius:thumb.r, flexShrink:0, background:broken?'#FEE2E2':'#DBEAFE', opacity: broken ? 0.35 : 1 }} onError={()=>setBroken(true)} />}
        <button type="button" onClick={()=>fileRef.current?.click()} disabled={busy}
          style={{ display:'flex', alignItems:'center', gap:4, padding:btnPad, background:'#EFF6FF', color:'#1E40AF', border:'1px solid #BFDBFE', borderRadius:6, cursor:busy?'wait':'pointer', fontSize, whiteSpace:'nowrap', flexShrink:0, fontWeight:500 }}>
          <Upload size={size==='sm'?11:12}/> {busy ? 'Uploading…' : (value ? 'Replace' : 'Upload')}
        </button>
        <input ref={fileRef} type="file" accept="image/*" onChange={e=>pickFile(e.target.files?.[0])} style={{ display:'none' }} />
        <input className="inp" value={value || ''} onChange={e=>onChange(e.target.value)}
          placeholder="or paste URL"
          style={{ flex:1, minWidth:0, fontSize, padding: size==='sm' ? '5px 8px' : undefined, borderColor: broken ? '#FCA5A5' : undefined }} />
        {value && (
          <button type="button" onClick={()=>onChange('')} title="Clear URL"
            style={{ padding: size==='sm' ? '5px 7px' : '6px 8px', background:'#FEF2F2', color:'#DC2626', border:'1px solid #FECACA', borderRadius:6, cursor:'pointer', flexShrink:0, fontSize, lineHeight:1 }}>
            <X size={size==='sm'?11:12}/>
          </button>
        )}
      </div>
      {broken && !err && (
        <div style={{ fontSize:11, color:'#B45309', background:'#FEF3C7', border:'1px solid #FDE68A', borderRadius:4, padding:'4px 6px', marginTop:2, lineHeight:1.35 }}>
          Image failed to load (file missing or URL broken). Click ✕ to clear, then re-upload.
        </div>
      )}
      {err && <div style={{ fontSize:11, color:'#DC2626', background:'#FEF2F2', border:'1px solid #FECACA', borderRadius:4, padding:'4px 6px', marginTop:2, lineHeight:1.35 }}>{err}</div>}
    </div>
  );
}

// ─── Projects Editor ──────────────────────────────────────────────────────────
function ProjectsEditor({ data, setLocal, setDirty }) {
  const [expandedId, setExpandedId] = useState(null);
  const [filter, setFilter] = useState('all');
  const [page, setPage] = useState(1);
  const [dragId, setDragId] = useState(null);
  const [dragOverId, setDragOverId] = useState(null);
  const PER_PAGE = 10;
  const projects = data.projects || [];

  // Reorder the global projects array so `fromId` lands just before `toId`.
  const reorder = (fromId, toId) => {
    if (fromId === toId) return;
    setLocal(prev => {
      const n = JSON.parse(JSON.stringify(prev));
      const list = n.projects;
      const from = list.findIndex(p => p.id === fromId);
      const to = list.findIndex(p => p.id === toId);
      if (from === -1 || to === -1) return prev;
      const [moved] = list.splice(from, 1);
      const insertAt = from < to ? to - 1 : to;
      list.splice(insertAt, 0, moved);
      return n;
    });
    setDirty(true);
  };

  const remove = i => {
    const removedId = projects[i]?.id;
    setLocal(p=>{const n=JSON.parse(JSON.stringify(p));n.projects.splice(i,1);return n;});
    setDirty(true);
    if (expandedId === removedId) setExpandedId(null);
  };
  const edit = (i,key,val) => { setLocal(p=>{const n=JSON.parse(JSON.stringify(p));n.projects[i][key]=val;return n;}); setDirty(true); };
  const add = () => {
    setLocal(p => {
      const n = JSON.parse(JSON.stringify(p));
      const list = n.projects || (n.projects = []);
      const nextId = list.reduce((m, x) => Math.max(m, Number(x.id) || 0), 0) + 1;
      const num = String(list.length + 1).padStart(2, '0');
      list.push({
        id: nextId, type: 'website', siteType: '', num,
        title: 'New Project', client: '', year: String(new Date().getFullYear()),
        url: '', tagline: '', tags: [], images: [],
        metrics: JSON.parse(JSON.stringify(DEFAULT_METRICS)),
        compatibility: JSON.parse(JSON.stringify(DEFAULT_COMPAT)),
        security: JSON.parse(JSON.stringify(DEFAULT_SECURITY)),
      });
      setExpandedId(nextId);
      setFilter('all');
      setPage(Math.ceil(list.length / PER_PAGE));
      return n;
    });
    setDirty(true);
  };

  const counts = {
    all:     projects.length,
    website: projects.filter(p => p.type === 'website').length,
    logo:    projects.filter(p => p.type === 'logo').length,
    seo:     projects.filter(p => p.type === 'seo').length,
    app:     projects.filter(p => p.type === 'app').length,
    tool:    projects.filter(p => p.type === 'tool' || p.type === 'software').length,
  };
  const filterTabs = [
    { id:'all',     label:'All' },
    { id:'website', label:'Websites' },
    { id:'app',     label:'Apps' },
    { id:'tool',    label:'Software' },
    { id:'logo',    label:'Logo & Identity' },
    { id:'seo',     label:'SEO' },
  ];
  const indexed = projects.map((p, i) => ({ p, origIndex: i }));
  const filteredRows = filter === 'all'
    ? indexed
    : filter === 'tool'
      ? indexed.filter(({ p }) => p.type === 'tool' || p.type === 'software')
      : indexed.filter(({ p }) => p.type === filter);
  const totalPages = Math.max(1, Math.ceil(filteredRows.length / PER_PAGE));
  const currentPage = Math.min(Math.max(1, page), totalPages);
  const pageRows = filteredRows.slice((currentPage - 1) * PER_PAGE, currentPage * PER_PAGE);
  const changeFilter = (f) => { setFilter(f); setPage(1); };

  // images sub-editor
  const [platformPhotoTabs, setPlatformPhotoTabs] = useState({});
  const addImage = (i) => { setLocal(p=>{const n=JSON.parse(JSON.stringify(p));n.projects[i].images=[...(n.projects[i].images||[]),''];return n;}); setDirty(true); };
  const editImage = (pi,ii,val) => { setLocal(p=>{const n=JSON.parse(JSON.stringify(p));n.projects[pi].images[ii]=val;return n;}); setDirty(true); };
  const removeImage = (pi,ii) => { setLocal(p=>{const n=JSON.parse(JSON.stringify(p));n.projects[pi].images.splice(ii,1);return n;}); setDirty(true); };

  const addPlatformImage = (pi, plat) => {
    setLocal(prev => {
      const n = JSON.parse(JSON.stringify(prev));
      const proj = n.projects[pi];
      if (!proj.platformImages) proj.platformImages = {};
      if (!Array.isArray(proj.platformImages[plat])) {
        proj.platformImages[plat] = (plat === proj.platforms?.[0] && proj.images) ? [...proj.images] : [];
      }
      proj.platformImages[plat].push('');
      if (plat === proj.platforms?.[0]) {
        proj.images = [...proj.platformImages[plat]];
      }
      return n;
    });
    setDirty(true);
  };

  const editPlatformImage = (pi, plat, ii, val) => {
    setLocal(prev => {
      const n = JSON.parse(JSON.stringify(prev));
      const proj = n.projects[pi];
      if (!proj.platformImages) proj.platformImages = {};
      if (!Array.isArray(proj.platformImages[plat])) {
        proj.platformImages[plat] = (plat === proj.platforms?.[0] && proj.images) ? [...proj.images] : [];
      }
      proj.platformImages[plat][ii] = val;
      if (plat === proj.platforms?.[0]) {
        proj.images = [...proj.platformImages[plat]];
      }
      return n;
    });
    setDirty(true);
  };

  const removePlatformImage = (pi, plat, ii) => {
    setLocal(prev => {
      const n = JSON.parse(JSON.stringify(prev));
      const proj = n.projects[pi];
      if (proj.platformImages && Array.isArray(proj.platformImages[plat])) {
        proj.platformImages[plat].splice(ii, 1);
        if (plat === proj.platforms?.[0]) {
          proj.images = [...proj.platformImages[plat]];
        }
      }
      return n;
    });
    setDirty(true);
  };

  return (
    <>
      <SectionHead title="Projects" subtitle={`${projects.length} projects · click a row to expand and edit`} />
      <div style={{ display:'flex', flexWrap:'wrap', gap:8, alignItems:'center', marginBottom:12 }}>
        <button onClick={add} className="btn-primary" style={{ display:'inline-flex', alignItems:'center', gap:6, padding:'8px 14px', borderRadius:8, fontSize:13 }}>
          <Plus size={13}/> Add Project
        </button>
      </div>

      {/* Filter tabs */}
      <div style={{ display:'flex', flexWrap:'wrap', gap:6, marginBottom:14, paddingBottom:10, borderBottom:'1px solid #DBEAFE' }}>
        {filterTabs.map(t => {
          const active = filter === t.id;
          return (
            <button key={t.id} onClick={() => changeFilter(t.id)} className="mono"
              style={{ display:'inline-flex', alignItems:'center', gap:6, padding:'6px 14px', borderRadius:99, border:`1.5px solid ${active ? '#1E40AF' : '#BFDBFE'}`, background: active ? '#1E40AF' : '#fff', color: active ? '#fff' : '#1E40AF', fontSize:11, textTransform:'uppercase', letterSpacing:'0.08em', cursor:'pointer', transition:'all .15s' }}>
              {t.label} <span style={{ opacity:.7 }}>({counts[t.id] ?? 0})</span>
            </button>
          );
        })}
      </div>

      {filteredRows.length === 0 && (
        <div style={{ padding:'24px 16px', background:'#F8FAFC', border:'1px dashed #CBD5E1', borderRadius:10, textAlign:'center', color:'#64748B', fontSize:13, marginBottom:12 }}>
          No projects in this category. Use the <strong>+ Add Project</strong> button and change the Project Type in the form.
        </div>
      )}

      {pageRows.length > 1 && (
        <div className="mono" style={{ fontSize:10, color:'#64748B', marginBottom:8, textTransform:'uppercase', letterSpacing:'0.08em', display:'flex', alignItems:'center', gap:6 }}>
          <GripVertical size={12} color="#94A3B8"/> Drag the handle on any row to reorder projects. The public site follows this order.
        </div>
      )}

      {pageRows.map(({ p, origIndex: i }) => {
        const isDragging = dragId === p.id;
        const isDragOver = dragOverId === p.id && dragId !== p.id;
        const badgeBg = (typeof ST_COLORS !== 'undefined' && ST_COLORS[p.siteType]) || '#64748B';
        return (
        <div key={p.id}
          onDragOver={e => {
            if (dragId == null || dragId === p.id) return;
            e.preventDefault();
            e.dataTransfer.dropEffect = 'move';
            if (dragOverId !== p.id) setDragOverId(p.id);
          }}
          onDragLeave={() => { if (dragOverId === p.id) setDragOverId(null); }}
          onDrop={e => {
            e.preventDefault();
            if (dragId != null && dragId !== p.id) reorder(dragId, p.id);
            setDragId(null);
            setDragOverId(null);
          }}
          style={{ background:'#fff', borderRadius:12, border:`1px solid ${isDragOver ? '#1E40AF' : '#DBEAFE'}`, marginBottom:8, overflow:'hidden', opacity: isDragging ? 0.5 : 1, boxShadow: isDragOver ? '0 0 0 2px #BFDBFE' : 'none', transition:'border-color .15s, box-shadow .15s, opacity .15s' }}>
          <div style={{ display:'flex', alignItems:'center', gap:10, padding:'12px 16px', cursor:'pointer', background:expandedId===p.id?'#EFF6FF':'#fff', transition:'background .15s' }} onClick={()=>setExpandedId(expandedId===p.id?null:p.id)}>
            <span
              title="Drag to reorder"
              draggable
              onDragStart={e => {
                e.stopPropagation();
                setDragId(p.id);
                e.dataTransfer.effectAllowed = 'move';
                e.dataTransfer.setData('text/plain', String(p.id));
              }}
              onDragEnd={() => { setDragId(null); setDragOverId(null); }}
              onClick={e => e.stopPropagation()}
              style={{ display:'flex', alignItems:'center', justifyContent:'center', width:24, height:30, cursor:'grab', color:'#94A3B8', flexShrink:0, borderRadius:5, background: isDragging ? '#EFF6FF' : 'transparent' }}
              onMouseEnter={e => { e.currentTarget.style.background = '#EFF6FF'; e.currentTarget.style.color = '#1E40AF'; }}
              onMouseLeave={e => { e.currentTarget.style.background = isDragging ? '#EFF6FF' : 'transparent'; e.currentTarget.style.color = '#94A3B8'; }}>
              <GripVertical size={16}/>
            </span>
            <img src={p.images?.[0]||''} alt="" style={{ width:46, height:34, objectFit:'cover', borderRadius:6, flexShrink:0, background:'#DBEAFE' }} onError={e=>e.target.style.opacity='.3'} />
            <div style={{ flex:1, minWidth:0 }}>
              <div style={{ fontSize:14, fontWeight:600, color:'#0F172A', whiteSpace:'nowrap', overflow:'hidden', textOverflow:'ellipsis' }}>{p.title}</div>
              <div style={{ display:'flex', gap:6, marginTop:2, alignItems:'center', flexWrap:'wrap' }}>
                <span className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#3B82F6' }}>{p.type}</span>
                {Array.isArray(p.platforms) && p.platforms.length > 0 ? (
                  p.platforms.map(plat => (
                    <span key={plat} className="mono" style={{ fontSize:9.5, padding:'1px 6px', borderRadius:99, background:'#F1F5F9', color:'#334155', border:'1px solid #CBD5E1' }}>
                      {plat === 'MacBook' ? ' ' : plat === 'Linux' ? '🐧 ' : plat === 'Windows' ? '⊞ ' : '📱 '}{plat}
                    </span>
                  ))
                ) : p.platform ? (
                  <span className="mono" style={{ fontSize:9.5, padding:'1px 6px', borderRadius:99, background:'#F1F5F9', color:'#334155', border:'1px solid #CBD5E1' }}>
                    {p.platform}
                  </span>
                ) : null}
                {p.siteType && <span className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#fff', background: badgeBg, padding:'1px 7px', borderRadius:99 }}>{p.siteType}</span>}
                {(() => {
                  let totalImgs = (p.images?.length || 0);
                  if (p.platformImages) {
                    const counts = Object.values(p.platformImages).map(arr => Array.isArray(arr) ? arr.length : 0);
                    if (counts.length > 0) totalImgs = Math.max(totalImgs, ...counts);
                  }
                  return totalImgs > 0 ? <span className="mono" style={{ fontSize:10, color:'#60A5FA' }}>📷 {totalImgs}</span> : null;
                })()}
              </div>
            </div>
            <div style={{ display:'flex', gap:5, flexShrink:0 }}>
              <button onClick={e=>{e.stopPropagation();remove(i);}} style={{ padding:'5px 8px', background:'#FEF2F2', color:'#DC2626', border:'1px solid #FECACA', borderRadius:6, cursor:'pointer' }}><Trash2 size={12}/></button>
              {expandedId===p.id ? <ChevronUp size={15} color="#64748B"/> : <ChevronDown size={15} color="#64748B"/>}
            </div>
          </div>

          {expandedId === p.id && (
            <div style={{ padding:'16px', borderTop:'1px solid #EFF6FF', background:'#FAFCFF' }}>
              <div style={{ display:'grid', gridTemplateColumns:'1fr 1fr', gap:10, marginBottom:10 }}>
                <Field label="Title"><input className="inp" value={p.title||''} onChange={e=>edit(i,'title',e.target.value)} /></Field>
                <Field label="Client"><input className="inp" value={p.client||''} onChange={e=>edit(i,'client',e.target.value)} /></Field>
                <Field label="Year"><input className="inp" value={p.year||''} onChange={e=>edit(i,'year',e.target.value)} /></Field>
                <Field label="URL"><input className="inp" value={p.url||''} onChange={e=>edit(i,'url',e.target.value)} /></Field>
              </div>

              <div style={{ display:'grid', gridTemplateColumns:'1fr 1fr 1fr', gap:10, marginBottom:10 }}>
                <Field label="Project Type">
                  <select className="inp" value={p.type||'website'} onChange={e=>{
                    const nt = e.target.value;
                    setLocal(prev => {
                      const n = JSON.parse(JSON.stringify(prev));
                      const proj = n.projects[i];
                      proj.type = nt;
                      if (nt === 'logo' && !Array.isArray(proj.palette)) proj.palette = ['#1E40AF','#3B82F6','#EFF6FF','#0F172A','#93C5FD'];
                      if (nt === 'seo' && !proj.seoData) proj.seoData = { before:0, after:0, growth:'0%', keywords1:0, keywords3:0, keywords10:0, domainAuthority:0, period:'' };
                      if (nt === 'app' && !proj.appData) proj.appData = { downloads:'', rating:0, reviews:'', platforms:['iOS','Android'], dau:'' };
                      if (nt === 'website' || nt === 'tool' || nt === 'software') {
                        if (!proj.metrics) proj.metrics = JSON.parse(JSON.stringify(DEFAULT_METRICS));
                        if (!proj.compatibility) proj.compatibility = JSON.parse(JSON.stringify(DEFAULT_COMPAT));
                        if (!proj.security) proj.security = JSON.parse(JSON.stringify(DEFAULT_SECURITY));
                      }
                      return n;
                    });
                    setDirty(true);
                  }} style={{ cursor:'pointer' }}>
                    <option value="website">Website</option>
                    <option value="app">App (Desktop / Mobile)</option>
                    <option value="software">Software / SaaS Platform</option>
                    <option value="tool">Tool</option>
                    <option value="logo">Logo & Identity</option>
                    <option value="seo">SEO Campaign</option>
                  </select>
                </Field>
                <Field label="Platform & Multi-Variant Support">
                  <div style={{ display:'flex', flexWrap:'wrap', gap:6, marginBottom:6 }}>
                    {['MacBook', 'Linux', 'Windows', 'iOS', 'Android', 'Web'].map(platName => {
                      const isSelected = Array.isArray(p.platforms)
                        ? p.platforms.includes(platName)
                        : (p.platform || '').toLowerCase().includes(platName.toLowerCase());
                      return (
                        <button
                          key={platName}
                          type="button"
                          onClick={() => {
                            let current = Array.isArray(p.platforms) && p.platforms.length > 0
                              ? [...p.platforms]
                              : (p.platform ? p.platform.split(',').map(s=>s.trim()).filter(Boolean) : []);
                            let updated;
                            if (isSelected) {
                              updated = current.filter(x => x !== platName);
                            } else {
                              updated = [...current, platName];
                            }
                            edit(i, 'platforms', updated);
                            edit(i, 'platform', updated.join(', '));
                          }}
                          className="mono"
                          style={{
                            fontSize:10.5,
                            padding:'3px 8px',
                            borderRadius:99,
                            cursor:'pointer',
                            border: isSelected ? '1.5px solid #1E40AF' : '1px solid #CBD5E1',
                            background: isSelected ? '#1E40AF' : '#FFFFFF',
                            color: isSelected ? '#FFFFFF' : '#475569',
                            fontWeight: isSelected ? 700 : 500,
                            display:'inline-flex',
                            alignItems:'center',
                            gap:4
                          }}
                        >
                          {platName === 'MacBook' && ' '}
                          {platName === 'Linux' && '🐧 '}
                          {platName === 'Windows' && '⊞ '}
                          {platName === 'iOS' && '📱 '}
                          {platName === 'Android' && '🤖 '}
                          {platName === 'Web' && '🌐 '}
                          <span>{platName}</span>
                          <span style={{ opacity:0.8 }}>{isSelected ? '✓' : '+'}</span>
                        </button>
                      );
                    })}
                  </div>
                  <input className="inp" value={p.platform||''} onChange={e=>{
                    const val = e.target.value;
                    edit(i, 'platform', val);
                    const plats = val.split(',').map(s=>s.trim()).filter(Boolean);
                    if (plats.length > 1) edit(i, 'platforms', plats);
                  }} placeholder="e.g. MacBook, Linux, Windows" />
                  {Array.isArray(p.platforms) && p.platforms.length > 1 && (
                    <div style={{ fontSize:10.5, color:'#2563EB', marginTop:4, fontWeight:600 }}>
                      ⚡ Multi-platform app active! You can upload screenshots separately for each platform below.
                    </div>
                  )}
                </Field>
                <Field label="Site Type / Category">
                  <select className="inp" value={p.siteType||''} onChange={e=>edit(i,'siteType',e.target.value)} style={{ cursor:'pointer' }}>
                    <option value="">— Select category —</option>
                    {SITE_TYPES.map(st=><option key={st} value={st}>{st}</option>)}
                    {p.type==='logo' && <option value="Brand Identity">Brand Identity</option>}
                    {p.type==='seo' && <option value="SEO Campaign">SEO Campaign</option>}
                    {p.type==='app' && <option value="Mobile App">Mobile App</option>}
                  </select>
                </Field>
              </div>

              <div style={{ display:'grid', gridTemplateColumns:'1fr 1fr', gap:10, marginBottom:10 }}>
                <Field label="Display Type / Pill (e.g. macOS Native App, eCommerce Store)">
                  <input className="inp" value={p.displayType||''} onChange={e=>edit(i,'displayType',e.target.value)} placeholder="e.g. eCommerce Store, MacBook App" />
                </Field>
                <Field label="Impact Pill (e.g. +165% Online Sales, 50,000+ Downloads)">
                  <input className="inp" value={p.impact||''} onChange={e=>edit(i,'impact',e.target.value)} placeholder="e.g. +165% Online Sales" />
                </Field>
              </div>

              <Field label="Business Summary / Tagline">
                <textarea className="inp" rows={2} value={p.businessSummary || p.tagline || ''} onChange={e=>{ edit(i,'businessSummary',e.target.value); edit(i,'tagline',e.target.value); }} placeholder="Brief summary of what this business does and what was delivered" />
              </Field>

              <div style={{ display:'grid', gridTemplateColumns:'1fr 1fr', gap:10, marginBottom:10 }}>
                <Field label="The Challenge">
                  <textarea className="inp" rows={2} value={p.challenge||''} onChange={e=>edit(i,'challenge',e.target.value)} placeholder="What obstacle or issue did the client face?" />
                </Field>
                <Field label="Our Solution">
                  <textarea className="inp" rows={2} value={p.solution||''} onChange={e=>edit(i,'solution',e.target.value)} placeholder="How did Techpenta solve it?" />
                </Field>
              </div>

              <Field label="Tags (comma separated)">
                <TagsInput value={p.tags||[]} onChange={v=>edit(i,'tags',v)} />
              </Field>

              {/* Images carousel editor with Multi-Platform support */}
              {(() => {
                const isMultiPlatform = Array.isArray(p.platforms) && p.platforms.length > 1;
                const currentPlat = isMultiPlatform ? (platformPhotoTabs[p.id] || p.platforms[0]) : null;
                const activeImgs = isMultiPlatform
                  ? ((p.platformImages && Array.isArray(p.platformImages[currentPlat]))
                      ? p.platformImages[currentPlat]
                      : (currentPlat === p.platforms[0] ? (p.images || []) : []))
                  : (p.images || []);

                return (
                  <Field label={isMultiPlatform ? "Photos (Multi-Platform: Upload screenshots per platform)" : "Photos (upload or paste URL — carousel)"}>
                    <div style={{ background:'#F8FAFC', borderRadius:8, padding:12, border:'1px solid #E2E8F0' }}>
                      {isMultiPlatform && (
                        <div style={{ display:'flex', flexWrap:'wrap', gap:6, marginBottom:12, paddingBottom:8, borderBottom:'1px solid #E2E8F0' }}>
                          {p.platforms.map(plat => {
                            const isCur = currentPlat === plat;
                            const count = (p.platformImages && Array.isArray(p.platformImages[plat]))
                              ? p.platformImages[plat].length
                              : (plat === p.platforms[0] ? (p.images?.length || 0) : 0);
                            return (
                              <button
                                key={plat}
                                type="button"
                                onClick={() => setPlatformPhotoTabs(prev => ({ ...prev, [p.id]: plat }))}
                                className="mono"
                                style={{
                                  display:'inline-flex',
                                  alignItems:'center',
                                  gap:6,
                                  padding:'6px 12px',
                                  borderRadius:8,
                                  border: isCur ? '1.5px solid #1E40AF' : '1px solid #CBD5E1',
                                  background: isCur ? '#EFF6FF' : '#FFFFFF',
                                  color: isCur ? '#1E40AF' : '#475569',
                                  fontWeight: isCur ? 700 : 500,
                                  fontSize:11.5,
                                  cursor:'pointer'
                                }}
                              >
                                <span>{plat === 'MacBook' ? '' : plat === 'Linux' ? '🐧' : plat === 'Windows' ? '⊞' : '📱'}</span>
                                <span>{plat} Screenshots</span>
                                <span style={{ fontSize:9.5, padding:'1px 6px', borderRadius:99, background: isCur ? '#1E40AF' : '#E2E8F0', color: isCur ? '#fff' : '#475569', fontWeight:700 }}>
                                  {count}
                                </span>
                              </button>
                            );
                          })}
                        </div>
                      )}

                      {activeImgs.map((img, ii) => (
                        <div key={ii} style={{ display:'flex', gap:7, marginBottom:7, alignItems:'center' }}>
                          <ImageInput
                            value={img}
                            onChange={v => {
                              if (isMultiPlatform) editPlatformImage(i, currentPlat, ii, v);
                              else editImage(i, ii, v);
                            }}
                          />
                          <button
                            type="button"
                            onClick={() => {
                              if (isMultiPlatform) removePlatformImage(i, currentPlat, ii);
                              else removeImage(i, ii);
                            }}
                            style={{ padding:'6px', background:'#FEF2F2', color:'#DC2626', border:'1px solid #FECACA', borderRadius:6, cursor:'pointer', flexShrink:0 }}
                          >
                            <Trash2 size={12}/>
                          </button>
                        </div>
                      ))}

                      <button
                        type="button"
                        onClick={() => {
                          if (isMultiPlatform) addPlatformImage(i, currentPlat);
                          else addImage(i);
                        }}
                        style={{ display:'flex', alignItems:'center', gap:5, padding:'6px 12px', background:'#EFF6FF', color:'#1E40AF', border:'1px solid #BFDBFE', borderRadius:7, cursor:'pointer', fontSize:12, marginTop:4 }}
                      >
                        <Plus size={12}/> Add {isMultiPlatform ? `${currentPlat} Photo` : 'Photo'}
                      </button>
                      <div style={{ fontSize:11, color:'#94A3B8', marginTop:8 }}>
                        {isMultiPlatform
                          ? `Screenshots uploaded for ${currentPlat} will be displayed on the ${currentPlat} project card and detail popup. Uploads are auto-resized to 1600px.`
                          : 'Multiple photos → auto-play carousel on the portfolio card and project detail. Uploads are auto-resized to 1600px.'}
                      </div>
                    </div>
                  </Field>
                );
              })()}

              {/* Video (plays in project popup only) */}
              <Field label="Video (plays in project popup only — leave empty for photos-only)">
                <div style={{ background:'#F8FAFC', borderRadius:8, padding:12, border:'1px solid #E2E8F0' }}>
                  <VideoInput value={p.videoUrl||''} onChange={v=>edit(i,'videoUrl',v)} />
                  {p.videoUrl && parseVideo(p.videoUrl) && (
                    <div style={{ fontSize:11, color:'#059669', marginTop:8 }}>
                      ✓ Valid video — type: <strong>{parseVideo(p.videoUrl).type}</strong>. Shows in the project popup instead of the photo carousel. Card thumbnail still uses Photos.
                    </div>
                  )}
                  {p.videoUrl && !parseVideo(p.videoUrl) && (
                    <div style={{ fontSize:11, color:'#DC2626', marginTop:8 }}>⚠ Not a recognized video URL.</div>
                  )}
                  {!p.videoUrl && (
                    <div style={{ fontSize:11, color:'#94A3B8', marginTop:8 }}>Upload an .mp4 / .webm / .mov file, or paste a YouTube / Vimeo / direct video URL. Max 200 MB.</div>
                  )}
                </div>
              </Field>

              {/* Logo palette — logo only */}
              {p.type === 'logo' && (
                <Field label="Brand Palette (5 hex colors)">
                  <div style={{ display:'grid', gridTemplateColumns:'repeat(5,1fr)', gap:8 }}>
                    {(p.palette || ['#1E40AF','#3B82F6','#EFF6FF','#0F172A','#93C5FD']).map((c, ci) => (
                      <div key={ci} style={{ display:'flex', flexDirection:'column', alignItems:'center', gap:5 }}>
                        <input type="color" value={c} onChange={e=>{
                          setLocal(prev => {
                            const n = JSON.parse(JSON.stringify(prev));
                            if (!Array.isArray(n.projects[i].palette)) n.projects[i].palette = ['#1E40AF','#3B82F6','#EFF6FF','#0F172A','#93C5FD'];
                            n.projects[i].palette[ci] = e.target.value;
                            return n;
                          });
                          setDirty(true);
                        }} style={{ width:'100%', height:44, border:'1px solid #DBEAFE', borderRadius:8, cursor:'pointer', background:'#fff' }} />
                        <input className="inp" value={c} onChange={e=>{
                          setLocal(prev => {
                            const n = JSON.parse(JSON.stringify(prev));
                            if (!Array.isArray(n.projects[i].palette)) n.projects[i].palette = ['#1E40AF','#3B82F6','#EFF6FF','#0F172A','#93C5FD'];
                            n.projects[i].palette[ci] = e.target.value;
                            return n;
                          });
                          setDirty(true);
                        }} style={{ fontSize:11, padding:'4px 6px', fontFamily:'monospace', textAlign:'center' }} />
                      </div>
                    ))}
                  </div>
                </Field>
              )}

              {/* SEO data — seo only */}
              {p.type === 'seo' && (
                <div style={{ background:'#F0F9FF', borderRadius:10, padding:14, border:'1px solid #BAE6FD', marginBottom:10 }}>
                  <div className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#0369A1', marginBottom:10 }}>SEO Campaign Data</div>
                  <div style={{ display:'grid', gridTemplateColumns:'1fr 1fr 1fr', gap:10 }}>
                    {[
                      { k:'before', label:'Traffic Before (/mo)', type:'number' },
                      { k:'after',  label:'Traffic After (/mo)', type:'number' },
                      { k:'growth', label:'Growth % (e.g. 1349%)', type:'text' },
                      { k:'keywords1',  label:'Keywords in Top 1', type:'number' },
                      { k:'keywords3',  label:'Keywords in Top 3', type:'number' },
                      { k:'keywords10', label:'Keywords in Top 10', type:'number' },
                      { k:'domainAuthority', label:'Domain Authority', type:'number' },
                      { k:'period', label:'Period (e.g. 12 months)', type:'text' },
                    ].map(f => (
                      <Field key={f.k} label={f.label}>
                        <input className="inp" type={f.type} value={(p.seoData||{})[f.k] ?? ''} onChange={e=>{
                          const v = f.type === 'number' ? Number(e.target.value) || 0 : e.target.value;
                          setLocal(prev => {
                            const n = JSON.parse(JSON.stringify(prev));
                            if (!n.projects[i].seoData) n.projects[i].seoData = {};
                            n.projects[i].seoData[f.k] = v;
                            return n;
                          });
                          setDirty(true);
                        }} />
                      </Field>
                    ))}
                  </div>
                </div>
              )}

              {/* App data — app only */}
              {p.type === 'app' && (
                <div style={{ background:'#EEF2FF', borderRadius:10, padding:14, border:'1px solid #C7D2FE', marginBottom:10 }}>
                  <div className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#3730A3', marginBottom:10 }}>Mobile App Data</div>
                  <div style={{ display:'grid', gridTemplateColumns:'1fr 1fr 1fr', gap:10 }}>
                    {[
                      { k:'downloads', label:'Downloads (e.g. 45K)', type:'text' },
                      { k:'rating',    label:'Store Rating (0–5)', type:'number', step:'0.1' },
                      { k:'reviews',   label:'Reviews (e.g. 1.8K)', type:'text' },
                      { k:'dau',       label:'Daily Active Users',  type:'text' },
                    ].map(f => (
                      <Field key={f.k} label={f.label}>
                        <input className="inp" type={f.type} step={f.step} value={(p.appData||{})[f.k] ?? ''} onChange={e=>{
                          const v = f.type === 'number' ? Number(e.target.value) || 0 : e.target.value;
                          setLocal(prev => {
                            const n = JSON.parse(JSON.stringify(prev));
                            if (!n.projects[i].appData) n.projects[i].appData = {};
                            n.projects[i].appData[f.k] = v;
                            return n;
                          });
                          setDirty(true);
                        }} />
                      </Field>
                    ))}
                    <Field label="Platforms (comma separated)">
                      <input className="inp" value={((p.appData||{}).platforms||[]).join(', ')} onChange={e=>{
                        const arr = e.target.value.split(',').map(t=>t.trim()).filter(Boolean);
                        setLocal(prev => {
                          const n = JSON.parse(JSON.stringify(prev));
                          if (!n.projects[i].appData) n.projects[i].appData = {};
                          n.projects[i].appData.platforms = arr;
                          return n;
                        });
                        setDirty(true);
                      }} />
                    </Field>
                  </div>
                </div>
              )}

              {/* Responsive screenshots — website only */}
              {p.type === 'website' && (
                <>
                <div style={{ marginTop:4 }}>
                  <div className="mono" style={{ fontSize:11, textTransform:'uppercase', letterSpacing:'0.1em', color:'#3B82F6', marginBottom:12, display:'flex', alignItems:'center', gap:6 }}>
                    <Smartphone size={12}/> Responsive Screenshots
                  </div>
                  <div style={{ display:'grid', gridTemplateColumns:'1fr 1fr 1fr', gap:10 }}>
                    {[
                      { key:'mobile',  label:'Mobile', icon:Smartphone, hint:'320–767px' },
                      { key:'tablet',  label:'Tablet',  icon:Tablet,     hint:'768–1023px' },
                      { key:'desktop', label:'Desktop', icon:Monitor,    hint:'1024–4K' },
                    ].map(dev => {
                      const devShots = (p.responsiveShots||{})[dev.key] || [];
                      const addShot = () => {
                        setLocal(prev => {
                          const n = JSON.parse(JSON.stringify(prev));
                          if (!n.projects[i].responsiveShots) n.projects[i].responsiveShots = {};
                          if (!n.projects[i].responsiveShots[dev.key]) n.projects[i].responsiveShots[dev.key] = [];
                          n.projects[i].responsiveShots[dev.key].push('');
                          return n;
                        });
                        setDirty(true);
                      };
                      const editShot = (si, val) => {
                        setLocal(prev => {
                          const n = JSON.parse(JSON.stringify(prev));
                          n.projects[i].responsiveShots[dev.key][si] = val;
                          return n;
                        });
                        setDirty(true);
                      };
                      const removeShot = (si) => {
                        setLocal(prev => {
                          const n = JSON.parse(JSON.stringify(prev));
                          n.projects[i].responsiveShots[dev.key].splice(si, 1);
                          return n;
                        });
                        setDirty(true);
                      };

                      return (
                        <div key={dev.key} style={{ background:'#F8FAFC', borderRadius:8, padding:10, border:'1px solid #E2E8F0' }}>
                          <div style={{ display:'flex', alignItems:'center', gap:5, marginBottom:8 }}>
                            <dev.icon size={12} color="#3B82F6"/>
                            <span style={{ fontSize:12, fontWeight:600, color:'#0F172A' }}>{dev.label}</span>
                            <span className="mono" style={{ fontSize:9, color:'#94A3B8', marginLeft:'auto' }}>{dev.hint}</span>
                          </div>
                          {devShots.map((src, si) => (
                            <div key={si} style={{ display:'flex', gap:5, marginBottom:5, alignItems:'center' }}>
                              <ImageInput value={src} onChange={v=>editShot(si,v)} size="sm" />
                              <button onClick={()=>removeShot(si)} style={{ padding:'4px', background:'#FEF2F2', color:'#DC2626', border:'1px solid #FECACA', borderRadius:5, cursor:'pointer', flexShrink:0 }}><Trash2 size={11}/></button>
                            </div>
                          ))}
                          <button onClick={addShot} style={{ display:'flex', alignItems:'center', gap:4, padding:'4px 10px', background:'#EFF6FF', color:'#1E40AF', border:'1px solid #BFDBFE', borderRadius:6, cursor:'pointer', fontSize:11, width:'100%', justifyContent:'center', marginTop:2 }}>
                            <Plus size={11}/> Add
                          </button>
                        </div>
                      );
                    })}
                  </div>
                  <div style={{ fontSize:11, color:'#94A3B8', marginTop:6 }}>Screenshots appear as thumbnails in the project detail → clickable lightbox with device frame.</div>
                </div>
                <div style={{ background:'#F8FAFF', borderRadius:10, padding:14, border:'1px solid #DBEAFE', marginTop:10 }}>
                  <div className="mono" style={{ fontSize:10, textTransform:'uppercase', color:'#3B82F6', marginBottom:12 }}>Browser & OS Compatibility</div>
                  {['browsers','os'].map(section => {
                    const options = section === 'browsers' ? ALL_BROWSERS : ALL_OS;
                    const current = (p.compatibility || DEFAULT_COMPAT)[section] || [];
                    const getStatus = (name) => (current.find(x=>x.name===name)||{}).status || null;
                    const toggle = (name, status) => {
                      setLocal(prev => {
                        const n = JSON.parse(JSON.stringify(prev));
                        if (!n.projects[i].compatibility) n.projects[i].compatibility = JSON.parse(JSON.stringify(DEFAULT_COMPAT));
                        const arr = n.projects[i].compatibility[section];
                        const idx = arr.findIndex(x=>x.name===name);
                        if (status === null) { if (idx>=0) arr.splice(idx,1); }
                        else if (idx>=0) { arr[idx].status = status; }
                        else { arr.push({ name, status }); }
                        return n;
                      });
                      setDirty(true);
                    };
                    return (
                      <div key={section} style={{ marginBottom: section==='browsers'?14:0 }}>
                        <div className="mono" style={{ fontSize:9, textTransform:'uppercase', color:'#64748B', marginBottom:6 }}>{section==='browsers'?'Browsers':'Operating Systems'}</div>
                        <div style={{ display:'flex', flexWrap:'wrap', gap:6 }}>
                          {options.map(name => {
                            const meta = COMPAT_META[name] || {};
                            const st = getStatus(name);
                            const active = st !== null;
                            return (
                              <div key={name} style={{ display:'flex', alignItems:'center', gap:0, borderRadius:8, border:`1.5px solid ${active ? (meta.color||'#3B82F6') : '#CBD5E1'}`, overflow:'hidden', background: active ? (meta.bg||'#EFF6FF') : '#F8FAFC' }}>
                                <div style={{ display:'flex', alignItems:'center', gap:5, padding:'5px 8px' }}>
                                  {meta.svg}
                                  <span style={{ fontSize:11, color:'#0F172A', fontWeight:500 }}>{name}</span>
                                </div>
                                <select
                                  value={st||''}
                                  onChange={e => toggle(name, e.target.value||null)}
                                  style={{ fontSize:10, border:'none', borderLeft:`1px solid ${active?(meta.color||'#3B82F6')+'44':'#E2E8F0'}`, background:'transparent', padding:'5px 6px', cursor:'pointer', color: st==='pass'?'#16A34A':st==='warn'?'#D97706':st==='fail'?'#DC2626':'#94A3B8', fontWeight:600, outline:'none' }}
                                >
                                  <option value="">Off</option>
                                  <option value="pass">✓ Pass</option>
                                  <option value="warn">⚠ Warn</option>
                                  <option value="fail">✗ Fail</option>
                                </select>
                              </div>
                            );
                          })}
                        </div>
                      </div>
                    );
                  })}
                </div>
              </>
              )}
            </div>
          )}
        </div>
        );
      })}

      {/* Pagination */}
      {filteredRows.length > PER_PAGE && (
        <div style={{ display:'flex', alignItems:'center', justifyContent:'space-between', gap:12, marginTop:14, padding:'10px 4px', flexWrap:'wrap' }}>
          <span className="mono" style={{ fontSize:11, color:'#64748B', textTransform:'uppercase', letterSpacing:'0.08em' }}>
            Showing {(currentPage - 1) * PER_PAGE + 1}–{Math.min(currentPage * PER_PAGE, filteredRows.length)} of {filteredRows.length}
          </span>
          <div style={{ display:'flex', gap:4, alignItems:'center', flexWrap:'wrap' }}>
            <button onClick={() => setPage(Math.max(1, currentPage - 1))} disabled={currentPage === 1}
              style={{ padding:'6px 12px', borderRadius:6, border:'1px solid #BFDBFE', background: currentPage===1 ? '#F1F5F9' : '#fff', color: currentPage===1 ? '#94A3B8' : '#1E40AF', cursor: currentPage===1 ? 'not-allowed' : 'pointer', fontSize:12, display:'inline-flex', alignItems:'center', gap:4 }}>
              <ChevronLeft size={13}/> Prev
            </button>
            {Array.from({ length: totalPages }, (_, idx) => idx + 1).map(pnum => (
              <button key={pnum} onClick={() => setPage(pnum)}
                style={{ minWidth:32, padding:'6px 10px', borderRadius:6, border:`1px solid ${pnum===currentPage ? '#1E40AF' : '#BFDBFE'}`, background: pnum===currentPage ? '#1E40AF' : '#fff', color: pnum===currentPage ? '#fff' : '#1E40AF', cursor:'pointer', fontSize:12, fontWeight: pnum===currentPage ? 600 : 400 }}>
                {pnum}
              </button>
            ))}
            <button onClick={() => setPage(Math.min(totalPages, currentPage + 1))} disabled={currentPage === totalPages}
              style={{ padding:'6px 12px', borderRadius:6, border:'1px solid #BFDBFE', background: currentPage===totalPages ? '#F1F5F9' : '#fff', color: currentPage===totalPages ? '#94A3B8' : '#1E40AF', cursor: currentPage===totalPages ? 'not-allowed' : 'pointer', fontSize:12, display:'inline-flex', alignItems:'center', gap:4 }}>
              Next <ChevronRight size={13}/>
            </button>
          </div>
        </div>
      )}
    </>
  );
}
