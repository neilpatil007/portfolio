import { randomBytes, createHash } from 'node:crypto';
import { writeFile, mkdir, readFile, rename, stat } from 'node:fs/promises';
import { createReadStream, statSync } from 'node:fs';
import { resolve, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import nodemailer from 'nodemailer';

const __dirname = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = __dirname;
const UPLOAD_DIR = resolve(PROJECT_ROOT, 'public', 'projects');
const DIST_UPLOAD_DIR = resolve(PROJECT_ROOT, 'dist', 'projects');
const DATA_FILE = resolve(PROJECT_ROOT, 'data.json');

const MAX_UPLOAD_BYTES = 200 * 1024 * 1024;
const MAX_DATA_BYTES = 16 * 1024 * 1024;
const MAX_QUOTE_BYTES = 32 * 1024 * 1024;  // 32 MB to fit base64-encoded attachments (~24 MB raw)

let _transporter = null;
function getTransporter() {
  if (_transporter) return _transporter;
  _transporter = nodemailer.createTransport({
    host: process.env.SMTP_HOST,
    port: Number(process.env.SMTP_PORT) || 465,
    secure: String(process.env.SMTP_SECURE || 'true') === 'true',
    auth: { user: process.env.SMTP_USER, pass: process.env.SMTP_PASS },
  });
  return _transporter;
}

function escapeHtml(s) {
  return String(s ?? '').replace(/[&<>"']/g, c => ({ '&':'&amp;', '<':'&lt;', '>':'&gt;', '"':'&quot;', "'":'&#39;' }[c]));
}

function quoteHtml(a) {
  const rows = [
    ['Service', a.service],
    ['Industry', a.industry],
    ['Platform', a.platform],
    ['WP Editor', a.wpEditor],
    ['App Platform', a.appPlatform],
    ['Logo Kind', a.logoKind],
    ['Existing site', a.existingUrl],
  ].filter(([, v]) => v);
  const tableRows = rows.map(([k, v]) =>
    `<tr><td style="padding:6px 12px;color:#64748B;font-size:12px;text-transform:uppercase;letter-spacing:.06em;border-bottom:1px solid #E2E8F0;">${escapeHtml(k)}</td><td style="padding:6px 12px;color:#0F172A;font-size:14px;border-bottom:1px solid #E2E8F0;">${escapeHtml(v)}</td></tr>`
  ).join('');
  const desc = a.description ? `<div style="margin-top:18px;"><div style="font-size:12px;color:#64748B;text-transform:uppercase;letter-spacing:.06em;margin-bottom:6px;">Description</div><div style="white-space:pre-wrap;color:#0F172A;font-size:14px;line-height:1.6;background:#F8FAFC;border:1px solid #E2E8F0;border-radius:8px;padding:12px;">${escapeHtml(a.description)}</div></div>` : '';
  const attachList = (a._attachmentsMeta && a._attachmentsMeta.length)
    ? `<div style="margin-top:18px;"><div style="font-size:12px;color:#64748B;text-transform:uppercase;letter-spacing:.06em;margin-bottom:6px;">Attachments (${a._attachmentsMeta.length})</div><ul style="margin:0;padding-left:18px;color:#0F172A;font-size:13.5px;line-height:1.7;">${a._attachmentsMeta.map(at => `<li>${escapeHtml(at.name)} <span style="color:#94A3B8;">— ${(at.size/1024).toFixed(1)} KB</span></li>`).join('')}</ul></div>`
    : '';
  return `<div style="font-family:-apple-system,Segoe UI,Roboto,sans-serif;max-width:600px;margin:0 auto;padding:24px;background:#fff;">
    <h2 style="color:#0F172A;margin:0 0 4px;">New quote request</h2>
    <p style="color:#64748B;margin:0 0 18px;">From <strong>${escapeHtml(a.name || 'Unknown')}</strong> &lt;${escapeHtml(a.email || '')}&gt;</p>
    <table style="border-collapse:collapse;width:100%;border:1px solid #E2E8F0;border-radius:8px;overflow:hidden;">${tableRows}</table>
    ${desc}
    ${attachList}
    <p style="color:#94A3B8;font-size:12px;margin-top:22px;">Submitted via portfolio.techpenta.com</p>
  </div>`;
}

// ─── Feature detection: fetch a URL and detect website capabilities ───────────
const FEATURE_CACHE = new Map();
const FEATURE_CACHE_TTL = 60 * 60 * 1000;
const FEATURE_TIMEOUT_MS = 9000;

const FEATURE_DEFS = [
  { key:'https',       label:'HTTPS / SSL Secured',     priority:100, test: c => c.url.startsWith('https://'),
    detail:'Encrypted connection' },
  { key:'responsive',  label:'Mobile Responsive',        priority:99, test: c => /<meta[^>]+name=["']viewport["']/i.test(c.html),
    detail:'Adaptive viewport meta' },
  { key:'seo',         label:'SEO Optimized',            priority:95, test: c => /<meta[^>]+name=["']description["']/i.test(c.html) && /<title[^>]*>[^<]+<\/title>/i.test(c.html),
    detail:'Title + description meta' },
  { key:'og',          label:'Social Media Cards',       priority:88, test: c => /<meta[^>]+property=["']og:/i.test(c.html),
    detail:'Open Graph / Twitter' },
  { key:'schema',      label:'Schema.org Markup',        priority:82, test: c => /application\/ld\+json/i.test(c.html) || /itemtype=["']https?:\/\/schema\.org/i.test(c.html),
    detail:'Structured data for Google' },
  { key:'analytics',   label:'Analytics Tracking',       priority:80, test: c => /(googletagmanager\.com|google-analytics\.com|gtag\(|_gaq|fbq\(|hotjar|clarity\.ms)/i.test(c.html),
    detail:'GA / GTM / Pixel' },
  { key:'ecommerce',   label:'E-commerce / Cart',        priority:90, test: c => /(add[-\s_]?to[-\s_]?cart|woocommerce|shopify|cdn\.shopify|snipcart|checkout)/i.test(c.html),
    detail:'Shopping cart enabled' },
  { key:'contact',     label:'Contact Form',             priority:78, test: c => /<form[^>]*>[\s\S]*?(name=["'](?:email|e-?mail)["']|type=["']email["'])[\s\S]*?<\/form>/i.test(c.html) || /contact[-_]?form/i.test(c.html),
    detail:'Lead capture enabled' },
  { key:'chat',        label:'Live Chat Widget',         priority:76, test: c => /(tawk\.to|intercom|crisp\.chat|drift\.com|livechatinc|tidio|zopim|hubspot.*chat)/i.test(c.html),
    detail:'Real-time customer chat' },
  { key:'whatsapp',    label:'WhatsApp / Click-to-Call', priority:74, test: c => /(wa\.me\/|api\.whatsapp|whatsapp:\/\/|href=["']tel:)/i.test(c.html),
    detail:'Direct contact buttons' },
  { key:'social',      label:'Social Media Links',       priority:72, test: c => {
      const hits = ['facebook.com','instagram.com','twitter.com','x.com','linkedin.com','youtube.com','tiktok.com','pinterest.com'].filter(d => c.html.includes(d));
      return hits.length >= 2;
    }, detail:'Multi-platform presence' },
  { key:'newsletter',  label:'Newsletter Signup',        priority:68, test: c => /(mailchimp|mc-embedded|klaviyo|substack|convertkit|sendinblue|brevo|subscribe[-_]?form)/i.test(c.html),
    detail:'Email capture' },
  { key:'multilang',   label:'Multi-language Support',   priority:84, test: c => /<link[^>]+hreflang=/i.test(c.html) || /lang-switcher|language-selector/i.test(c.html),
    detail:'Hreflang or switcher' },
  { key:'blog',        label:'Blog / Articles',          priority:60, test: c => /(\/blog\/|\/post\/|<article[\s>])/i.test(c.html),
    detail:'Editorial content' },
  { key:'search',      label:'Site Search',              priority:58, test: c => /<input[^>]+type=["']search["']/i.test(c.html) || /name=["']s["']/i.test(c.html) || /\?s=|\/search\?/i.test(c.html),
    detail:'On-site search bar' },
  { key:'cdn',         label:'CDN Delivery',             priority:70, test: c => (c.headers['cf-ray'] || c.headers['x-served-by'] || c.headers['x-cdn'] || c.headers['x-cache']) || /cloudflare|cdn\.|akamai|fastly/i.test(c.html),
    detail:'Cloudflare / Fastly / Akamai' },
  { key:'cookie',      label:'Cookie Consent Banner',    priority:54, test: c => /(cookiebot|onetrust|cookieyes|cookie[-_]?consent|cookie[-_]?banner|gdpr)/i.test(c.html),
    detail:'GDPR compliant' },
  { key:'lazyimg',     label:'Lazy-loaded Images',       priority:62, test: c => /loading=["']lazy["']/i.test(c.html),
    detail:'Faster page loads' },
  { key:'fonts',       label:'Custom Web Fonts',         priority:48, test: c => /(fonts\.googleapis|fonts\.gstatic|@font-face|fonts\.cdnfonts|use\.typekit)/i.test(c.html),
    detail:'Brand typography' },
  { key:'video',       label:'Video Content',            priority:56, test: c => /(<video[\s>]|youtube\.com\/embed|player\.vimeo\.com|<source[^>]+type=["']video)/i.test(c.html),
    detail:'Embedded video media' },
  { key:'gallery',     label:'Image Gallery / Slider',   priority:52, test: c => /(swiper|slick-carousel|owl-carousel|glide\.js|splide|carousel|lightbox)/i.test(c.html),
    detail:'Visual showcase' },
  { key:'login',       label:'Member / Login Area',      priority:64, test: c => /(\/login|\/signin|\/account|\/my-account|<input[^>]+type=["']password["'])/i.test(c.html),
    detail:'User accounts' },
  { key:'pwa',         label:'PWA / Web App',            priority:46, test: c => /<link[^>]+rel=["']manifest["']/i.test(c.html) || /serviceWorker\.register/i.test(c.html),
    detail:'Installable web app' },
  { key:'favicon',     label:'Branded Favicon',          priority:40, test: c => /<link[^>]+rel=["'](?:icon|shortcut icon|apple-touch-icon)/i.test(c.html),
    detail:'Tab branding' },
];

function fetchUrl(target) {
  return new Promise((resolve, reject) => {
    let u;
    try { u = new URL(target); } catch (e) { return reject(new Error('invalid url')); }
    if (!/^https?:$/.test(u.protocol)) return reject(new Error('only http/https allowed'));
    if (/^(127\.|10\.|192\.168\.|169\.254\.|0\.)/.test(u.hostname) || u.hostname === 'localhost') {
      return reject(new Error('blocked host'));
    }
    import(u.protocol === 'https:' ? 'node:https' : 'node:http').then(({ default: lib }) => {
      const req = lib.get(u.toString(), {
        timeout: FEATURE_TIMEOUT_MS,
        headers: {
          'User-Agent': 'TechpentaFeatureBot/1.0 (+https://portfolio.techpenta.com)',
          'Accept': 'text/html,application/xhtml+xml',
          'Accept-Language': 'en-US,en;q=0.9',
        },
      }, res => {
        if (res.statusCode >= 300 && res.statusCode < 400 && res.headers.location) {
          res.resume();
          return fetchUrl(new URL(res.headers.location, u).toString()).then(resolve, reject);
        }
        if (res.statusCode >= 400) { res.resume(); return reject(new Error('HTTP ' + res.statusCode)); }
        const chunks = []; let total = 0;
        res.on('data', c => { total += c.length; if (total > 2 * 1024 * 1024) { req.destroy(); return; } chunks.push(c); });
        res.on('end', () => resolve({ url: u.toString(), html: Buffer.concat(chunks).toString('utf8'), headers: res.headers }));
        res.on('error', reject);
      });
      req.on('timeout', () => { req.destroy(new Error('timeout')); });
      req.on('error', reject);
    }).catch(reject);
  });
}

function featuresHandler(req, res, next) {
  if (req.method !== 'GET') return next();
  (async () => {
    try {
      const u = new URL(req.url, 'http://x');
      const target = u.searchParams.get('url');
      if (!target) return json(res, 400, { error: 'missing url' });
      const cached = FEATURE_CACHE.get(target);
      if (cached && Date.now() - cached.t < FEATURE_CACHE_TTL) {
        return json(res, 200, { features: cached.features, cached: true });
      }
      const ctx = await fetchUrl(target);
      const detected = FEATURE_DEFS
        .filter(f => { try { return !!f.test(ctx); } catch { return false; } })
        .sort((a, b) => b.priority - a.priority)
        .slice(0, 10)
        .map(f => ({ key: f.key, label: f.label, detail: f.detail }));
      FEATURE_CACHE.set(target, { t: Date.now(), features: detected });
      json(res, 200, { features: detected, cached: false });
    } catch (e) {
      json(res, 502, { error: e.message || 'fetch failed' });
    }
  })();
}

// ─── Device screenshot proxy + cache ──────────────────────────────────────────
const SHOT_DIR = resolve(PROJECT_ROOT, 'public', 'screenshots');
const SHOT_DIST_DIR = resolve(PROJECT_ROOT, 'dist', 'screenshots');
const DEVICE_DIM = { mobile:{w:414,h:896}, tablet:{w:820,h:1180}, desktop:{w:1280,h:900} };
const MIN_REAL_BYTES = 12000;        // anything smaller is mshots' "generating…" placeholder
const MAX_RETRIES = 10;
const RETRY_DELAY_MS = 2500;
const FETCH_USER_AGENTS = [
  'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36',
  'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
  'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36',
];

const _shotInflight = new Map();

function fetchBytes(url, ua) {
  return new Promise((res, rej) => {
    let u; try { u = new URL(url); } catch (e) { return rej(e); }
    import(u.protocol === 'https:' ? 'node:https' : 'node:http').then(({ default: lib }) => {
      const req = lib.get(u.toString(), {
        timeout: 25000,
        headers: {
          'User-Agent': ua,
          'Accept': 'image/avif,image/webp,image/png,image/jpeg,image/*,*/*',
          'Accept-Language': 'en-US,en;q=0.9',
        },
      }, r => {
        if (r.statusCode >= 300 && r.statusCode < 400 && r.headers.location) {
          r.resume();
          return fetchBytes(new URL(r.headers.location, u).toString(), ua).then(res, rej);
        }
        if (r.statusCode >= 400) { r.resume(); return rej(new Error('HTTP ' + r.statusCode)); }
        const chunks = []; let total = 0;
        r.on('data', c => { total += c.length; if (total > 8 * 1024 * 1024) { req.destroy(); return; } chunks.push(c); });
        r.on('end', () => res({ buf: Buffer.concat(chunks), type: r.headers['content-type'] || 'image/jpeg' }));
        r.on('error', rej);
      });
      req.on('timeout', () => req.destroy(new Error('timeout')));
      req.on('error', rej);
    }).catch(rej);
  });
}

async function generateScreenshot(targetUrl, device) {
  const dim = DEVICE_DIM[device] || DEVICE_DIM.desktop;
  const mshots = `https://s0.wp.com/mshots/v1/${encodeURIComponent(targetUrl)}?w=${dim.w}&h=${dim.h}`;
  let last = null;
  for (let i = 0; i < MAX_RETRIES; i++) {
    try {
      const ua = FETCH_USER_AGENTS[i % FETCH_USER_AGENTS.length];
      const r = await fetchBytes(mshots, ua);
      last = r;
      if (r.buf.length >= MIN_REAL_BYTES) return r;        // real screenshot
    } catch (e) { last = { err: e }; }
    await new Promise(r => setTimeout(r, RETRY_DELAY_MS));
  }
  if (last && last.buf) return last;                       // give up, return placeholder
  throw new Error(last?.err?.message || 'screenshot generation failed');
}

function shotCacheKey(targetUrl, device) {
  return createHash('sha256').update(`${device}:${targetUrl}`).digest('hex').slice(0, 24) + '-' + device;
}

async function ensureScreenshot(targetUrl, device) {
  const key = shotCacheKey(targetUrl, device);
  const ext = 'jpg';
  const filename = `${key}.${ext}`;
  const localPath = resolve(SHOT_DIR, filename);
  try { await stat(localPath); return { filename, fresh: false }; } catch {}
  if (_shotInflight.has(filename)) return _shotInflight.get(filename);
  const job = (async () => {
    await mkdir(SHOT_DIR, { recursive: true });
    await mkdir(SHOT_DIST_DIR, { recursive: true });
    const { buf } = await generateScreenshot(targetUrl, device);
    await writeFile(localPath, buf);
    try { await writeFile(resolve(SHOT_DIST_DIR, filename), buf); } catch {}
    return { filename, fresh: true };
  })();
  _shotInflight.set(filename, job);
  try { return await job; } finally { _shotInflight.delete(filename); }
}

function screenshotHandler(req, res, next) {
  if (req.method !== 'GET') return next();
  (async () => {
    try {
      const u = new URL(req.url, 'http://x');
      const target = u.searchParams.get('url');
      const device = (u.searchParams.get('device') || 'desktop').toLowerCase();
      if (!target) return json(res, 400, { error: 'missing url' });
      if (!DEVICE_DIM[device]) return json(res, 400, { error: 'invalid device' });
      let parsed; try { parsed = new URL(target); } catch { return json(res, 400, { error: 'bad url' }); }
      if (!/^https?:$/.test(parsed.protocol)) return json(res, 400, { error: 'http/https only' });
      if (/^(127\.|10\.|192\.168\.|169\.254\.|0\.)/.test(parsed.hostname) || parsed.hostname === 'localhost') {
        return json(res, 400, { error: 'blocked host' });
      }
      const { filename } = await ensureScreenshot(parsed.toString(), device);
      const path = resolve(SHOT_DIR, filename);
      const size = statSync(path).size;
      res.statusCode = 200;
      res.setHeader('Content-Type', 'image/jpeg');
      res.setHeader('Content-Length', size);
      res.setHeader('Cache-Control', 'public, max-age=86400, stale-while-revalidate=604800');
      createReadStream(path).pipe(res);
    } catch (e) {
      json(res, 502, { error: e.message || 'failed' });
    }
  })();
}

// ─── Embed-check: detect X-Frame-Options / CSP frame-ancestors blocking ───────
const _embedCache = new Map();
const EMBED_TTL = 30 * 60 * 1000;

function headRequest(url) {
  return new Promise((res, rej) => {
    let u; try { u = new URL(url); } catch (e) { return rej(e); }
    import(u.protocol === 'https:' ? 'node:https' : 'node:http').then(({ default: lib }) => {
      const req = lib.request(u.toString(), {
        method: 'GET',
        timeout: 8000,
        headers: { 'User-Agent': 'TechpentaEmbedCheck/1.0', 'Accept': 'text/html,*/*' },
      }, r => {
        if (r.statusCode >= 300 && r.statusCode < 400 && r.headers.location) {
          r.resume();
          return headRequest(new URL(r.headers.location, u).toString()).then(res, rej);
        }
        // We only need headers; abort body
        const headers = r.headers;
        r.resume();
        res({ headers, status: r.statusCode });
      });
      req.on('timeout', () => req.destroy(new Error('timeout')));
      req.on('error', rej);
      req.end();
    }).catch(rej);
  });
}

function checkEmbeddable(headers) {
  const xfo = String(headers['x-frame-options'] || '').toLowerCase().trim();
  if (xfo === 'deny') return { embeddable: false, reason: 'X-Frame-Options: DENY' };
  if (xfo === 'sameorigin') return { embeddable: false, reason: 'X-Frame-Options: SAMEORIGIN' };
  if (xfo.startsWith('allow-from')) return { embeddable: false, reason: 'X-Frame-Options restricts host' };
  const csp = String(headers['content-security-policy'] || '').toLowerCase();
  const m = csp.match(/frame-ancestors\s+([^;]+)/);
  if (m) {
    const directive = m[1].trim();
    if (/'none'/.test(directive)) return { embeddable: false, reason: 'CSP frame-ancestors: none' };
    if (/'self'/.test(directive) && !/[*]/.test(directive)) return { embeddable: false, reason: 'CSP frame-ancestors: self' };
  }
  return { embeddable: true };
}

function embedCheckHandler(req, res, next) {
  if (req.method !== 'GET') return next();
  (async () => {
    try {
      const u = new URL(req.url, 'http://x');
      const target = u.searchParams.get('url');
      if (!target) return json(res, 400, { error: 'missing url' });
      const cached = _embedCache.get(target);
      if (cached && Date.now() - cached.t < EMBED_TTL) return json(res, 200, { ...cached.v, cached: true });
      const { headers } = await headRequest(target);
      const v = checkEmbeddable(headers);
      _embedCache.set(target, { t: Date.now(), v });
      json(res, 200, v);
    } catch (e) {
      // On fetch failure, allow embed attempt — browser will decide.
      json(res, 200, { embeddable: true, reason: 'check failed: ' + e.message });
    }
  })();
}

function quoteHandler(req, res, next) {
  if (req.method !== 'POST') return next();
  (async () => {
    try {
      if (!process.env.SMTP_HOST || !process.env.SMTP_USER || !process.env.SMTP_PASS) {
        return json(res, 500, { error: 'SMTP not configured' });
      }
      const buf = await readBody(req, MAX_QUOTE_BYTES);
      const a = JSON.parse(buf.toString('utf8'));
      if (!a || typeof a !== 'object') return json(res, 400, { error: 'invalid payload' });
      if (!a.email || !/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(String(a.email).trim())) {
        return json(res, 400, { error: 'invalid email' });
      }
      const attachments = [];
      const files = Array.isArray(a.files) ? a.files : [];
      let totalAttachBytes = 0;
      for (const f of files.slice(0, 5)) {
        if (!f || typeof f.dataUrl !== 'string') continue;
        const m = f.dataUrl.match(/^data:([^;]+);base64,(.*)$/);
        if (!m) continue;
        const buf = Buffer.from(m[2], 'base64');
        if (buf.length > 10 * 1024 * 1024) continue;
        totalAttachBytes += buf.length;
        if (totalAttachBytes > 22 * 1024 * 1024) break;
        attachments.push({ filename: String(f.name || 'attachment').replace(/[^\w.\-() ]/g,'_').slice(0,120), content: buf, contentType: m[1] });
      }
      const safe = { ...a }; delete safe.files;
      const subject = `New Quote: ${a.service || 'Inquiry'}${a.industry ? ' · ' + a.industry : ''} — ${a.name || a.email}`;
      const info = await getTransporter().sendMail({
        from: `"Techpenta Portfolio" <${process.env.QUOTE_FROM || process.env.SMTP_USER}>`,
        to: process.env.QUOTE_TO || process.env.SMTP_USER,
        replyTo: `${a.name ? '"' + String(a.name).replace(/"/g,'') + '" ' : ''}<${a.email}>`,
        subject,
        html: quoteHtml({ ...safe, _attachmentsMeta: attachments.map(at => ({ name: at.filename, size: at.content.length })) }),
        text: JSON.stringify(safe, null, 2),
        attachments,
      });
      json(res, 200, { ok: true, id: info.messageId });
    } catch (e) {
      json(res, 500, { error: e.message });
    }
  })();
}

function readBody(req, limit) {
  return new Promise((res, rej) => {
    const chunks = [];
    let total = 0;
    req.on('data', (c) => {
      total += c.length;
      if (total > limit) { rej(new Error('payload too large')); req.destroy(); return; }
      chunks.push(c);
    });
    req.on('end', () => res(Buffer.concat(chunks)));
    req.on('error', rej);
  });
}

function json(res, status, obj) {
  res.statusCode = status;
  res.setHeader('Content-Type', 'application/json');
  res.setHeader('Cache-Control', 'no-store');
  res.end(JSON.stringify(obj));
}

const EXT_BY_MIME = {
  'image/jpeg': 'jpg',
  'image/jpg': 'jpg',
  'image/pjpeg': 'jpg',
  'image/png': 'png',
  'image/webp': 'webp',
  'image/gif': 'gif',
  'image/avif': 'avif',
  'image/svg+xml': 'svg',
  'video/mp4': 'mp4',
  'video/webm': 'webm',
  'video/ogg': 'ogv',
  'video/quicktime': 'mov',
  'video/x-matroska': 'mkv',
};

function uploadHandler(req, res, next) {
  if (req.method !== 'POST') return next();
  (async () => {
    try {
      await mkdir(UPLOAD_DIR, { recursive: true });
      await mkdir(DIST_UPLOAD_DIR, { recursive: true });
      const buf = await readBody(req, MAX_UPLOAD_BYTES);
      const ctype = (req.headers['content-type'] || '').split(';')[0].trim().toLowerCase();
      const ext = EXT_BY_MIME[ctype] || 'jpg';
      const isVideo = ctype.startsWith('video/');
      const id = randomBytes(6).toString('hex');
      const filename = `${isVideo ? 'vid' : 'img'}-${Date.now().toString(36)}-${id}.${ext}`;
      await writeFile(resolve(UPLOAD_DIR, filename), buf);
      await writeFile(resolve(DIST_UPLOAD_DIR, filename), buf);
      json(res, 200, { url: `/projects/${filename}` });
    } catch (e) {
      json(res, 500, { error: e.message });
    }
  })();
}

function dataHandler(req, res, next) {
  if (req.method === 'GET') {
    (async () => {
      try {
        const buf = await readFile(DATA_FILE);
        res.statusCode = 200;
        res.setHeader('Content-Type', 'application/json');
        res.setHeader('Cache-Control', 'no-store');
        res.end(buf);
      } catch (e) {
        if (e.code === 'ENOENT') return json(res, 404, { error: 'no data' });
        json(res, 500, { error: e.message });
      }
    })();
    return;
  }
  if (req.method === 'POST' || req.method === 'PUT') {
    (async () => {
      try {
        const buf = await readBody(req, MAX_DATA_BYTES);
        const parsed = JSON.parse(buf.toString('utf8'));
        if (!parsed || typeof parsed !== 'object' || Array.isArray(parsed)) {
          return json(res, 400, { error: 'payload must be an object' });
        }
        if (!Array.isArray(parsed.projects) || !parsed.hero || typeof parsed.hero !== 'object') {
          return json(res, 400, { error: 'payload missing required fields (hero, projects)' });
        }
        const tmp = DATA_FILE + '.tmp';
        await writeFile(tmp, buf);
        await rename(tmp, DATA_FILE);
        json(res, 200, { ok: true });
      } catch (e) {
        json(res, 400, { error: e.message });
      }
    })();
    return;
  }
  return next();
}

export default function uploadPlugin() {
  return {
    name: 'project-image-upload',
    configureServer(server) {
      server.middlewares.use('/api/upload', uploadHandler);
      server.middlewares.use('/api/data', dataHandler);
      server.middlewares.use('/api/quote', quoteHandler);
      server.middlewares.use('/api/features', featuresHandler);
      server.middlewares.use('/api/screenshot', screenshotHandler);
      server.middlewares.use('/api/embed-check', embedCheckHandler);
    },
    configurePreviewServer(server) {
      server.middlewares.use('/api/upload', uploadHandler);
      server.middlewares.use('/api/data', dataHandler);
      server.middlewares.use('/api/quote', quoteHandler);
      server.middlewares.use('/api/features', featuresHandler);
      server.middlewares.use('/api/screenshot', screenshotHandler);
      server.middlewares.use('/api/embed-check', embedCheckHandler);
    },
  };
}
