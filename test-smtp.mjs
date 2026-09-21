import nodemailer from 'nodemailer';
import { readFileSync } from 'node:fs';

// Load .env manually (no dotenv dep)
for (const line of readFileSync(new URL('./.env', import.meta.url), 'utf8').split('\n')) {
  const m = line.match(/^([A-Z_]+)=(.*)$/);
  if (m) process.env[m[1]] = m[2];
}

const t = nodemailer.createTransport({
  host: process.env.SMTP_HOST,
  port: Number(process.env.SMTP_PORT),
  secure: process.env.SMTP_SECURE === 'true',
  auth: { user: process.env.SMTP_USER, pass: process.env.SMTP_PASS },
});

console.log('Verifying SMTP…');
await t.verify();
console.log('Verified. Sending test email…');

const info = await t.sendMail({
  from: `"Techpenta Portfolio" <${process.env.SMTP_USER}>`,
  to: 'parthait2003@gmail.com',
  subject: 'SMTP test from portfolio.techpenta.com',
  text: 'This is a test email confirming SMTP delivery from the portfolio site is working. — Techpenta',
  html: `<div style="font-family:-apple-system,Segoe UI,Roboto,sans-serif;max-width:560px;margin:0 auto;padding:24px;background:#fff;">
    <h2 style="color:#0F172A;margin:0 0 6px;">SMTP test ✓</h2>
    <p style="color:#475569;line-height:1.6;">This is a test email confirming SMTP delivery from the portfolio site is working.</p>
    <p style="color:#94A3B8;font-size:12px;margin-top:18px;">Sent at ${new Date().toISOString()} via mail.techpenta.com:465 (SSL)</p>
  </div>`,
});
console.log('Sent:', info.messageId, '→', info.accepted);
