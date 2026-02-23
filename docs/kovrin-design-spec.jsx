import { useState } from "react";

// KOVRIN Design System + Sitemap + Wireframes
// Style: Dev-brutalist, border-radius: 0, AI-first, monospace-heavy

const COLORS = {
  bg: "#0A0A0B",
  surface: "#111113",
  surfaceHover: "#18181B",
  border: "#27272A",
  borderAccent: "#3F3F46",
  text: "#FAFAFA",
  textMuted: "#71717A",
  textDim: "#52525B",
  accent: "#10B981",     // Emerald — safety, trust, go
  accentDim: "#059669",
  accentBg: "rgba(16,185,129,0.08)",
  danger: "#EF4444",
  warning: "#F59E0B",
  blue: "#3B82F6",
  purple: "#8B5CF6",
  white: "#FFFFFF",
};

const fonts = {
  mono: "'JetBrains Mono', 'Fira Code', 'SF Mono', monospace",
  display: "'Space Grotesk', 'DM Sans', sans-serif",
  body: "'Inter', 'DM Sans', sans-serif",
};

// Actually, per the design skill, avoid Inter and Space Grotesk
// Let's use something more distinctive
const FONT_IMPORT = `
@import url('https://fonts.googleapis.com/css2?family=JetBrains+Mono:wght@400;500;600;700&family=DM+Sans:wght@400;500;600;700&family=Instrument+Sans:wght@400;500;600;700&display=swap');
`;

const Tab = ({ active, onClick, children, count }) => (
  <button
    onClick={onClick}
    style={{
      padding: "10px 20px",
      background: active ? COLORS.accent : "transparent",
      color: active ? COLORS.bg : COLORS.textMuted,
      border: `1px solid ${active ? COLORS.accent : COLORS.border}`,
      borderRadius: 0,
      fontFamily: "'JetBrains Mono', monospace",
      fontSize: "12px",
      fontWeight: active ? 700 : 500,
      cursor: "pointer",
      textTransform: "uppercase",
      letterSpacing: "0.05em",
      display: "flex",
      alignItems: "center",
      gap: "8px",
      transition: "all 0.15s ease",
    }}
  >
    {children}
    {count && (
      <span style={{
        background: active ? COLORS.bg : COLORS.border,
        color: active ? COLORS.accent : COLORS.textMuted,
        padding: "2px 6px",
        fontSize: "10px",
        fontWeight: 700,
      }}>{count}</span>
    )}
  </button>
);

const SectionTitle = ({ children, sub }) => (
  <div style={{ marginBottom: "24px" }}>
    <h2 style={{
      fontFamily: "'JetBrains Mono', monospace",
      fontSize: "20px",
      fontWeight: 700,
      color: COLORS.text,
      margin: 0,
      letterSpacing: "-0.02em",
    }}>
      <span style={{ color: COLORS.accent }}>/// </span>{children}
    </h2>
    {sub && (
      <p style={{
        fontFamily: "'DM Sans', sans-serif",
        fontSize: "14px",
        color: COLORS.textMuted,
        margin: "6px 0 0 0",
        lineHeight: 1.5,
      }}>{sub}</p>
    )}
  </div>
);

const Card = ({ title, children, accent, tag }) => (
  <div style={{
    background: COLORS.surface,
    border: `1px solid ${accent ? COLORS.accent : COLORS.border}`,
    borderLeft: accent ? `3px solid ${COLORS.accent}` : `1px solid ${COLORS.border}`,
    padding: "20px",
    marginBottom: "12px",
  }}>
    <div style={{ display: "flex", justifyContent: "space-between", alignItems: "center", marginBottom: "12px" }}>
      <h3 style={{
        fontFamily: "'JetBrains Mono', monospace",
        fontSize: "14px",
        fontWeight: 600,
        color: COLORS.text,
        margin: 0,
      }}>{title}</h3>
      {tag && (
        <span style={{
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: "10px",
          padding: "3px 8px",
          background: tag === "FREE" ? COLORS.accentBg : tag === "PRO" ? "rgba(59,130,246,0.1)" : "rgba(139,92,246,0.1)",
          color: tag === "FREE" ? COLORS.accent : tag === "PRO" ? COLORS.blue : COLORS.purple,
          border: `1px solid ${tag === "FREE" ? COLORS.accent : tag === "PRO" ? COLORS.blue : COLORS.purple}`,
          textTransform: "uppercase",
          fontWeight: 700,
        }}>{tag}</span>
      )}
    </div>
    <div style={{
      fontFamily: "'DM Sans', sans-serif",
      fontSize: "13px",
      color: COLORS.textMuted,
      lineHeight: 1.6,
    }}>{children}</div>
  </div>
);

// ============== SITEMAP TAB ==============
const SitemapView = () => (
  <div>
    <SectionTitle sub="Complete information architecture for kovrin.ai + app.kovrin.ai + docs.kovrin.dev">
      Sitemap
    </SectionTitle>

    <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: "16px" }}>
      <div>
        <div style={{
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: "11px",
          color: COLORS.accent,
          textTransform: "uppercase",
          letterSpacing: "0.1em",
          marginBottom: "12px",
          fontWeight: 700,
        }}>MARKETING — kovrin.ai</div>

        <Card title="/ — Homepage" accent>
          Hero: "Provable safety for AI agents" + live terminal demo<br/>
          Problem → Solution → How it works (3 steps) → Code example<br/>
          Social proof (GitHub stars, design partners) → CTA
        </Card>
        <Card title="/features">
          Constitutional Constraints, Formal Verification (TLA+),<br/>
          Merkle Audit Trail, Risk Routing, Human-in-the-loop,<br/>
          Compliance mapping (EU AI Act)
        </Card>
        <Card title="/pricing">
          Free (OSS) → Pro ($79/mo) → Enterprise (custom)<br/>
          Feature comparison table, FAQ
        </Card>
        <Card title="/docs → docs.kovrin.dev">
          Redirect to documentation site
        </Card>
        <Card title="/blog">
          Technical blog, launch announcements, case studies
        </Card>
        <Card title="/about">
          Story, team (just you for now), mission, open-source philosophy
        </Card>
        <Card title="/security">
          Security practices, responsible disclosure, audit reports
        </Card>
        <Card title="/changelog">
          Version history, auto-generated from GitHub releases
        </Card>
      </div>

      <div>
        <div style={{
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: "11px",
          color: COLORS.blue,
          textTransform: "uppercase",
          letterSpacing: "0.1em",
          marginBottom: "12px",
          fontWeight: 700,
        }}>APP — app.kovrin.ai</div>

        <Card title="/dashboard" tag="PRO">
          Agent overview: active pipelines, risk scores, recent events<br/>
          Real-time monitoring, alerts, health status
        </Card>
        <Card title="/agents" tag="PRO">
          List of registered agents, status, last activity<br/>
          Click → agent detail with full audit trail
        </Card>
        <Card title="/audit" tag="PRO">
          Merkle-verified audit log, filterable, exportable<br/>
          Compliance reports (EU AI Act, SOC 2)
        </Card>
        <Card title="/policies" tag="PRO">
          Constitutional constraints editor (visual + code)<br/>
          Risk profiles, approval workflows
        </Card>
        <Card title="/settings" tag="PRO">
          API keys, team management, billing, integrations
        </Card>

        <div style={{
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: "11px",
          color: COLORS.warning,
          textTransform: "uppercase",
          letterSpacing: "0.1em",
          margin: "24px 0 12px 0",
          fontWeight: 700,
        }}>DOCS — docs.kovrin.dev</div>

        <Card title="/getting-started" tag="FREE">
          5-minute quickstart, installation, first pipeline
        </Card>
        <Card title="/guides" tag="FREE">
          Integration guides: LangGraph, CrewAI, custom agents
        </Card>
        <Card title="/api-reference" tag="FREE">
          Auto-generated from docstrings, searchable
        </Card>
        <Card title="/concepts" tag="FREE">
          Architecture, TLA+ specs, Constitutional AI theory
        </Card>
      </div>
    </div>
  </div>
);

// ============== DESIGN SYSTEM TAB ==============
const ColorSwatch = ({ color, name, hex }) => (
  <div style={{ display: "flex", alignItems: "center", gap: "12px", marginBottom: "8px" }}>
    <div style={{
      width: "40px", height: "40px",
      background: color,
      border: `1px solid ${COLORS.border}`,
    }} />
    <div>
      <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "12px", color: COLORS.text, fontWeight: 600 }}>{name}</div>
      <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "11px", color: COLORS.textMuted }}>{hex}</div>
    </div>
  </div>
);

const DesignSystemView = () => (
  <div>
    <SectionTitle sub="Brutalist-dev aesthetic. Zero border-radius. Terminal-native. Trust through precision.">
      Design System
    </SectionTitle>

    <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: "24px" }}>
      <div>
        <Card title="Philosophy" accent>
          <strong style={{ color: COLORS.text }}>KOVRIN looks like a tool built by engineers, for engineers.</strong><br/><br/>
          No rounded corners. No gradients. No illustrations with floating people.<br/>
          Monospace everywhere that matters. Color only where it communicates.<br/>
          The UI itself should feel like a safety system — precise, predictable, trustworthy.<br/><br/>
          <span style={{ color: COLORS.accent }}>References:</span> Linear, Vercel (early), Warp terminal, Raycast, Supabase dashboard
        </Card>

        <Card title="Colors — Dark Mode Only (v1)">
          <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: "4px" }}>
            <ColorSwatch color="#0A0A0B" name="Background" hex="#0A0A0B" />
            <ColorSwatch color="#111113" name="Surface" hex="#111113" />
            <ColorSwatch color="#18181B" name="Surface Hover" hex="#18181B" />
            <ColorSwatch color="#27272A" name="Border" hex="#27272A" />
            <ColorSwatch color="#FAFAFA" name="Text" hex="#FAFAFA" />
            <ColorSwatch color="#71717A" name="Text Muted" hex="#71717A" />
            <ColorSwatch color="#10B981" name="Accent (Safety)" hex="#10B981" />
            <ColorSwatch color="#EF4444" name="Danger" hex="#EF4444" />
            <ColorSwatch color="#F59E0B" name="Warning" hex="#F59E0B" />
            <ColorSwatch color="#3B82F6" name="Info / Pro" hex="#3B82F6" />
          </div>
          <br/>
          <span style={{ color: COLORS.textDim, fontSize: "12px" }}>
            Emerald green = safety, trust, "all systems go". Nie generic purple AI vibe.
          </span>
        </Card>

        <Card title="Border Radius">
          <div style={{
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: "24px",
            fontWeight: 700,
            color: COLORS.accent,
            marginBottom: "8px",
          }}>0px</div>
          Everywhere. Buttons, cards, inputs, modals, badges, tooltips.<br/>
          Sharp edges = precision = safety. This is non-negotiable.
        </Card>
      </div>

      <div>
        <Card title="Typography">
          <div style={{ marginBottom: "16px" }}>
            <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "11px", color: COLORS.accent, marginBottom: "4px" }}>CODE / UI LABELS</div>
            <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "18px", color: COLORS.text }}>JetBrains Mono</div>
            <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "12px", color: COLORS.textMuted }}>Headings, labels, badges, nav, code blocks, data</div>
          </div>
          <div style={{ marginBottom: "16px" }}>
            <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "11px", color: COLORS.accent, marginBottom: "4px" }}>DISPLAY / HERO</div>
            <div style={{ fontFamily: "'Instrument Sans', sans-serif", fontSize: "18px", color: COLORS.text, fontWeight: 700 }}>Instrument Sans</div>
            <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "12px", color: COLORS.textMuted }}>Hero headlines, marketing pages, large statements</div>
          </div>
          <div>
            <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "11px", color: COLORS.accent, marginBottom: "4px" }}>BODY TEXT</div>
            <div style={{ fontFamily: "'DM Sans', sans-serif", fontSize: "18px", color: COLORS.text }}>DM Sans</div>
            <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "12px", color: COLORS.textMuted }}>Paragraphs, descriptions, blog content, long-form</div>
          </div>
        </Card>

        <Card title="Component Rules">
          <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "12px", lineHeight: 2 }}>
            <span style={{ color: COLORS.accent }}>border-radius:</span> <span style={{ color: COLORS.text }}>0</span><br/>
            <span style={{ color: COLORS.accent }}>border:</span> <span style={{ color: COLORS.text }}>1px solid #27272A</span><br/>
            <span style={{ color: COLORS.accent }}>focus-ring:</span> <span style={{ color: COLORS.text }}>2px solid #10B981</span><br/>
            <span style={{ color: COLORS.accent }}>buttons:</span> <span style={{ color: COLORS.text }}>uppercase, letter-spacing: 0.05em</span><br/>
            <span style={{ color: COLORS.accent }}>transitions:</span> <span style={{ color: COLORS.text }}>150ms ease, no bounce</span><br/>
            <span style={{ color: COLORS.accent }}>shadows:</span> <span style={{ color: COLORS.text }}>none (use borders instead)</span><br/>
            <span style={{ color: COLORS.accent }}>icons:</span> <span style={{ color: COLORS.text }}>Lucide (line), 18px default</span><br/>
            <span style={{ color: COLORS.accent }}>spacing:</span> <span style={{ color: COLORS.text }}>4px grid (4, 8, 12, 16, 20, 24, 32, 48)</span><br/>
            <span style={{ color: COLORS.accent }}>max-width:</span> <span style={{ color: COLORS.text }}>1200px (marketing), 100% (app)</span><br/>
          </div>
        </Card>

        <Card title="Recommended Stack">
          <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "12px", lineHeight: 2 }}>
            <span style={{ color: COLORS.accent }}>framework:</span> <span style={{ color: COLORS.text }}>Next.js 15 (App Router)</span><br/>
            <span style={{ color: COLORS.accent }}>styling:</span> <span style={{ color: COLORS.text }}>Tailwind CSS v4</span><br/>
            <span style={{ color: COLORS.accent }}>ui-lib:</span> <span style={{ color: COLORS.text }}>shadcn/ui (customized to 0 radius)</span><br/>
            <span style={{ color: COLORS.accent }}>icons:</span> <span style={{ color: COLORS.text }}>Lucide React</span><br/>
            <span style={{ color: COLORS.accent }}>animation:</span> <span style={{ color: COLORS.text }}>Framer Motion (minimal)</span><br/>
            <span style={{ color: COLORS.accent }}>docs:</span> <span style={{ color: COLORS.text }}>Fumadocs or Nextra</span><br/>
            <span style={{ color: COLORS.accent }}>hosting:</span> <span style={{ color: COLORS.text }}>Vercel (marketing + app)</span><br/>
            <span style={{ color: COLORS.accent }}>auth:</span> <span style={{ color: COLORS.text }}>Clerk or Auth.js</span><br/>
          </div>
        </Card>
      </div>
    </div>
  </div>
);

// ============== WIREFRAMES TAB ==============
const WireBox = ({ label, h, accent, children, dashed }) => (
  <div style={{
    border: `1px ${dashed ? "dashed" : "solid"} ${accent ? COLORS.accent : COLORS.border}`,
    height: h || "auto",
    display: "flex",
    flexDirection: "column",
    alignItems: "center",
    justifyContent: "center",
    padding: "12px",
    background: accent ? COLORS.accentBg : "transparent",
    position: "relative",
  }}>
    <span style={{
      fontFamily: "'JetBrains Mono', monospace",
      fontSize: "10px",
      color: accent ? COLORS.accent : COLORS.textDim,
      textTransform: "uppercase",
      letterSpacing: "0.05em",
      fontWeight: 600,
    }}>{label}</span>
    {children}
  </div>
);

const WireframesView = () => {
  const [page, setPage] = useState("home");

  return (
    <div>
      <SectionTitle sub="Low-fidelity wireframes showing layout, content hierarchy, and component placement">
        Wireframes
      </SectionTitle>

      <div style={{ display: "flex", gap: "8px", marginBottom: "24px", flexWrap: "wrap" }}>
        {[
          ["home", "Homepage"],
          ["features", "Features"],
          ["pricing", "Pricing"],
          ["dashboard", "Dashboard"],
        ].map(([id, label]) => (
          <Tab key={id} active={page === id} onClick={() => setPage(id)}>
            {label}
          </Tab>
        ))}
      </div>

      {page === "home" && (
        <div style={{
          background: COLORS.surface,
          border: `1px solid ${COLORS.border}`,
          padding: "24px",
          maxWidth: "700px",
        }}>
          {/* Nav */}
          <div style={{ display: "flex", justifyContent: "space-between", padding: "12px 0", borderBottom: `1px solid ${COLORS.border}`, marginBottom: "32px" }}>
            <span style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "12px", color: COLORS.accent, fontWeight: 700 }}>KOVRIN</span>
            <div style={{ display: "flex", gap: "16px" }}>
              {["Features", "Pricing", "Docs", "Blog", "GitHub"].map(i => (
                <span key={i} style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "10px", color: COLORS.textMuted }}>{i}</span>
              ))}
              <span style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "10px", color: COLORS.bg, background: COLORS.accent, padding: "2px 8px", fontWeight: 700 }}>GET STARTED</span>
            </div>
          </div>

          {/* Hero */}
          <WireBox label="Hero Section" h="200px" accent>
            <div style={{ textAlign: "center", marginTop: "8px" }}>
              <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "10px", color: COLORS.accent, marginBottom: "8px" }}>★ 1.2K GITHUB STARS</div>
              <div style={{ fontFamily: "'DM Sans', sans-serif", fontSize: "22px", color: COLORS.text, fontWeight: 700, lineHeight: 1.2 }}>Provable safety for<br/>AI agents in production</div>
              <div style={{ fontFamily: "'DM Sans', sans-serif", fontSize: "11px", color: COLORS.textMuted, marginTop: "8px" }}>Constitutional constraints + formal verification + cryptographic audit.<br/>Not guardrails. Guarantees.</div>
              <div style={{ display: "flex", gap: "8px", justifyContent: "center", marginTop: "12px" }}>
                <span style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "9px", color: COLORS.bg, background: COLORS.accent, padding: "4px 12px", fontWeight: 700 }}>pip install kovrin</span>
                <span style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "9px", color: COLORS.textMuted, border: `1px solid ${COLORS.border}`, padding: "4px 12px" }}>VIEW DOCS →</span>
              </div>
            </div>
          </WireBox>

          <div style={{ height: "8px" }} />

          {/* Terminal Demo */}
          <WireBox label="Live Terminal Demo — animated code example" h="120px">
            <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "9px", color: COLORS.textDim, textAlign: "left", width: "100%" }}>
              <span style={{ color: COLORS.textMuted }}>$</span> <span style={{ color: COLORS.accent }}>kovrin</span> run --intent "transfer $50K" --risk-profile strict<br/>
              <span style={{ color: COLORS.textMuted }}>[kovrin]</span> Risk: HIGH | Constitutional check: PASS<br/>
              <span style={{ color: COLORS.textMuted }}>[kovrin]</span> Approval required: human-in-the-loop triggered<br/>
              <span style={{ color: COLORS.textMuted }}>[kovrin]</span> Audit hash: 0x7f3a...b2c1 ✓ verified
            </div>
          </WireBox>

          <div style={{ height: "24px" }} />

          {/* 3 Steps */}
          <WireBox label="How It Works — 3 columns" h="100px">
            <div style={{ display: "flex", gap: "16px", width: "100%", marginTop: "4px" }}>
              {[
                ["01", "Define constraints", "Constitutional rules your agents must follow"],
                ["02", "Verify formally", "TLA+ proves safety before deployment"],
                ["03", "Monitor & audit", "Cryptographic trail of every decision"],
              ].map(([n, t, d]) => (
                <div key={n} style={{ flex: 1, textAlign: "center" }}>
                  <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "16px", color: COLORS.accent, fontWeight: 700 }}>{n}</div>
                  <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "9px", color: COLORS.text, fontWeight: 600 }}>{t}</div>
                  <div style={{ fontFamily: "'DM Sans', sans-serif", fontSize: "8px", color: COLORS.textDim }}>{d}</div>
                </div>
              ))}
            </div>
          </WireBox>

          <div style={{ height: "8px" }} />

          {/* Code Example */}
          <WireBox label="Code Example — syntax highlighted, copy button" h="90px">
            <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "9px", color: COLORS.textDim, textAlign: "left", width: "100%" }}>
              <span style={{ color: COLORS.purple }}>from</span> <span style={{ color: COLORS.text }}>kovrin</span> <span style={{ color: COLORS.purple }}>import</span> <span style={{ color: COLORS.text }}>Agent, Constitution</span><br/>
              <span style={{ color: COLORS.text }}>agent</span> = <span style={{ color: COLORS.blue }}>Agent</span>(model=<span style={{ color: COLORS.accent }}>"claude-sonnet"</span>)<br/>
              <span style={{ color: COLORS.text }}>agent</span>.constitution.add(<span style={{ color: COLORS.accent }}>"Never transfer &gt; $10K without approval"</span>)<br/>
              <span style={{ color: COLORS.text }}>result</span> = agent.run(intent=<span style={{ color: COLORS.accent }}>"Process payment"</span>)
            </div>
          </WireBox>

          <div style={{ height: "8px" }} />

          {/* Social Proof */}
          <WireBox label="Social Proof — logos, testimonials, GitHub stats" h="60px" dashed />

          <div style={{ height: "8px" }} />

          {/* CTA */}
          <WireBox label="Final CTA — 'Start building safer agents today'" h="60px" accent />

          <div style={{ height: "8px" }} />

          {/* Footer */}
          <WireBox label="Footer — links, GitHub, Discord, newsletter signup" h="50px" dashed />
        </div>
      )}

      {page === "features" && (
        <div style={{
          background: COLORS.surface,
          border: `1px solid ${COLORS.border}`,
          padding: "24px",
          maxWidth: "700px",
        }}>
          <WireBox label="Hero — 'Six layers of provable safety'" h="80px" accent />
          <div style={{ height: "12px" }} />

          <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: "8px" }}>
            {[
              ["Constitutional Constraints", "Define rules agents MUST follow. Not suggestions — enforced invariants."],
              ["Formal Verification (TLA+)", "Mathematical proof your safety properties hold. Before deployment, not after."],
              ["Merkle Audit Trail", "Every decision cryptographically signed. Tamper-proof. Compliance-ready."],
              ["Risk-Based Routing", "LOW → auto-execute. MEDIUM → monitor. HIGH → human approval. CRITICAL → block."],
              ["Human-in-the-Loop", "Configurable approval flows. Slack, email, dashboard. With SLA timers."],
              ["Compliance Mapping", "EU AI Act Article 14/12, SOC 2, HIPAA. Pre-mapped to KOVRIN features."],
            ].map(([t, d]) => (
              <WireBox key={t} label={t} h="80px">
                <div style={{ fontFamily: "'DM Sans', sans-serif", fontSize: "8px", color: COLORS.textDim, textAlign: "center", marginTop: "4px" }}>{d}</div>
              </WireBox>
            ))}
          </div>

          <div style={{ height: "12px" }} />
          <WireBox label="Architecture Diagram — interactive, zoomable" h="100px" dashed />
          <div style={{ height: "12px" }} />
          <WireBox label="Comparison Table — KOVRIN vs LangGraph vs CrewAI vs NeMo" h="80px" />
          <div style={{ height: "12px" }} />
          <WireBox label="CTA — 'See it in action' → docs quickstart" h="50px" accent />
        </div>
      )}

      {page === "pricing" && (
        <div style={{
          background: COLORS.surface,
          border: `1px solid ${COLORS.border}`,
          padding: "24px",
          maxWidth: "700px",
        }}>
          <WireBox label="Hero — 'Open-source core. Enterprise when you need it.'" h="60px" accent />
          <div style={{ height: "16px" }} />

          <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr 1fr", gap: "8px" }}>
            <div style={{ border: `1px solid ${COLORS.border}`, padding: "16px" }}>
              <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "12px", color: COLORS.accent, fontWeight: 700, marginBottom: "8px" }}>OPEN SOURCE</div>
              <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "20px", color: COLORS.text, fontWeight: 700 }}>$0</div>
              <div style={{ fontFamily: "'DM Sans', sans-serif", fontSize: "9px", color: COLORS.textMuted, marginTop: "8px", lineHeight: 1.6 }}>
                Core safety engine<br/>Constitutional constraints<br/>Basic audit trail<br/>CLI<br/>Community Discord<br/>MIT License
              </div>
              <div style={{ marginTop: "12px", fontFamily: "'JetBrains Mono', monospace", fontSize: "9px", color: COLORS.accent, border: `1px solid ${COLORS.accent}`, padding: "6px", textAlign: "center", fontWeight: 700 }}>
                pip install kovrin
              </div>
            </div>

            <div style={{ border: `2px solid ${COLORS.accent}`, padding: "16px", background: COLORS.accentBg }}>
              <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "12px", color: COLORS.blue, fontWeight: 700, marginBottom: "8px" }}>PRO</div>
              <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "20px", color: COLORS.text, fontWeight: 700 }}>$79<span style={{ fontSize: "12px", color: COLORS.textMuted }}>/mo</span></div>
              <div style={{ fontFamily: "'DM Sans', sans-serif", fontSize: "9px", color: COLORS.textMuted, marginTop: "8px", lineHeight: 1.6 }}>
                Everything in OSS +<br/>Dashboard & monitoring<br/>Compliance reports<br/>Team management<br/>Email support (48h)<br/>5 agents included
              </div>
              <div style={{ marginTop: "12px", fontFamily: "'JetBrains Mono', monospace", fontSize: "9px", color: COLORS.bg, background: COLORS.accent, padding: "6px", textAlign: "center", fontWeight: 700 }}>
                START FREE TRIAL
              </div>
            </div>

            <div style={{ border: `1px solid ${COLORS.border}`, padding: "16px" }}>
              <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "12px", color: COLORS.purple, fontWeight: 700, marginBottom: "8px" }}>ENTERPRISE</div>
              <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "20px", color: COLORS.text, fontWeight: 700 }}>Custom</div>
              <div style={{ fontFamily: "'DM Sans', sans-serif", fontSize: "9px", color: COLORS.textMuted, marginTop: "8px", lineHeight: 1.6 }}>
                Everything in Pro +<br/>SSO/SAML<br/>On-prem deployment<br/>Custom compliance<br/>SLA support (4h)<br/>Unlimited agents
              </div>
              <div style={{ marginTop: "12px", fontFamily: "'JetBrains Mono', monospace", fontSize: "9px", color: COLORS.purple, border: `1px solid ${COLORS.purple}`, padding: "6px", textAlign: "center", fontWeight: 700 }}>
                CONTACT SALES
              </div>
            </div>
          </div>

          <div style={{ height: "16px" }} />
          <WireBox label="Feature Comparison Table — detailed, all tiers" h="100px" />
          <div style={{ height: "12px" }} />
          <WireBox label="FAQ — accordion style, 8-10 questions" h="60px" dashed />
        </div>
      )}

      {page === "dashboard" && (
        <div style={{
          background: COLORS.surface,
          border: `1px solid ${COLORS.border}`,
          padding: "24px",
          maxWidth: "700px",
        }}>
          {/* App Nav */}
          <div style={{ display: "flex", borderBottom: `1px solid ${COLORS.border}`, paddingBottom: "8px", marginBottom: "16px" }}>
            <div style={{ display: "flex", gap: "16px", alignItems: "center" }}>
              <span style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "12px", color: COLORS.accent, fontWeight: 700 }}>◆ KOVRIN</span>
              {["Dashboard", "Agents", "Audit Log", "Policies", "Settings"].map(i => (
                <span key={i} style={{
                  fontFamily: "'JetBrains Mono', monospace",
                  fontSize: "10px",
                  color: i === "Dashboard" ? COLORS.text : COLORS.textMuted,
                  fontWeight: i === "Dashboard" ? 600 : 400,
                }}>{i}</span>
              ))}
            </div>
          </div>

          {/* Stats */}
          <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr 1fr 1fr", gap: "8px", marginBottom: "16px" }}>
            {[
              ["Active Agents", "12", COLORS.accent],
              ["Events (24h)", "1,847", COLORS.blue],
              ["Blocked", "3", COLORS.danger],
              ["Avg Risk Score", "0.23", COLORS.accent],
            ].map(([label, val, col]) => (
              <div key={label} style={{ border: `1px solid ${COLORS.border}`, padding: "12px" }}>
                <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "8px", color: COLORS.textDim, textTransform: "uppercase" }}>{label}</div>
                <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "18px", color: col, fontWeight: 700 }}>{val}</div>
              </div>
            ))}
          </div>

          {/* Main content */}
          <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: "8px" }}>
            <WireBox label="Real-time Event Stream" h="140px">
              <div style={{ fontFamily: "'JetBrains Mono', monospace", fontSize: "8px", color: COLORS.textDim, textAlign: "left", width: "100%", marginTop: "8px", lineHeight: 1.8 }}>
                <span style={{ color: COLORS.accent }}>✓</span> agent-7 | transfer $200 | LOW | auto<br/>
                <span style={{ color: COLORS.warning }}>⚠</span> agent-3 | delete records | HIGH | pending<br/>
                <span style={{ color: COLORS.accent }}>✓</span> agent-1 | query DB | LOW | auto<br/>
                <span style={{ color: COLORS.danger }}>✕</span> agent-5 | ext API call | CRIT | blocked<br/>
                <span style={{ color: COLORS.accent }}>✓</span> agent-2 | email send | MED | approved
              </div>
            </WireBox>

            <WireBox label="Risk Distribution Chart" h="140px" dashed>
              <div style={{ fontFamily: "'DM Sans', sans-serif", fontSize: "9px", color: COLORS.textDim }}>
                Histogram / bar chart showing<br/>risk score distribution across agents
              </div>
            </WireBox>
          </div>

          <div style={{ height: "8px" }} />
          <WireBox label="Agent Overview Table — name, status, last action, risk, audit hash" h="80px" />
          <div style={{ height: "8px" }} />
          <WireBox label="Recent Compliance Events — exportable, filterable" h="60px" dashed />
        </div>
      )}
    </div>
  );
};

// ============== CONTENT TAB ==============
const ContentView = () => (
  <div>
    <SectionTitle sub="Copy direction, tone of voice, key messaging for every page">
      Content Strategy
    </SectionTitle>

    <Card title="Voice & Tone" accent>
      <strong style={{ color: COLORS.text }}>Technical. Precise. Zero bullshit.</strong><br/><br/>
      KOVRIN doesn't say "empower" or "leverage" or "unlock potential".<br/>
      KOVRIN says exactly what it does: "Proves your safety constraints hold before deployment."<br/><br/>
      <span style={{ color: COLORS.accent }}>Tone:</span> Senior engineer explaining to another senior engineer.<br/>
      <span style={{ color: COLORS.accent }}>Not:</span> Marketing team explaining to a CTO at a conference.<br/><br/>
      Show code before words. Terminal output before diagrams. Proof before promises.
    </Card>

    <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: "12px" }}>
      <Card title="Homepage Hero Copy">
        <span style={{ color: COLORS.text, fontWeight: 600 }}>H1:</span> "Provable safety for AI agents in production"<br/>
        <span style={{ color: COLORS.text, fontWeight: 600 }}>Sub:</span> "Constitutional constraints. Formal verification. Cryptographic audit. Not guardrails — guarantees."<br/>
        <span style={{ color: COLORS.text, fontWeight: 600 }}>CTA 1:</span> "pip install kovrin" (copy-to-clipboard)<br/>
        <span style={{ color: COLORS.text, fontWeight: 600 }}>CTA 2:</span> "Read the docs →"<br/>
        <span style={{ color: COLORS.text, fontWeight: 600 }}>Social:</span> "★ {`{stars}`} on GitHub | Used by {`{n}`} teams"
      </Card>

      <Card title="Key Differentiators (use everywhere)">
        <span style={{ color: COLORS.accent }}>1.</span> Only framework with TLA+ formal verification<br/>
        <span style={{ color: COLORS.accent }}>2.</span> Merkle hash chain audit trail (tamper-proof)<br/>
        <span style={{ color: COLORS.accent }}>3.</span> Constitutional constraints (not prompts — invariants)<br/>
        <span style={{ color: COLORS.accent }}>4.</span> Risk-based routing with human-in-the-loop<br/>
        <span style={{ color: COLORS.accent }}>5.</span> EU AI Act pre-mapped compliance
      </Card>

      <Card title="SEO Keywords (target)">
        <span style={{ color: COLORS.text }}>Primary:</span> AI agent safety framework, AI safety open source<br/>
        <span style={{ color: COLORS.text }}>Secondary:</span> formal verification AI, EU AI Act compliance tool, AI audit trail, constitutional AI agents<br/>
        <span style={{ color: COLORS.text }}>Long-tail:</span> "how to add safety to LangGraph agents", "TLA+ for AI systems", "AI agent compliance EU"
      </Card>

      <Card title="Blog Content Calendar (Phase 1)">
        <span style={{ color: COLORS.accent }}>Week 3:</span> "Why We Built KOVRIN" (launch)<br/>
        <span style={{ color: COLORS.accent }}>Week 4:</span> "TLA+ Catches Safety Bugs" (technical)<br/>
        <span style={{ color: COLORS.accent }}>Week 6:</span> "EU AI Act Implementation Guide" (compliance)<br/>
        <span style={{ color: COLORS.accent }}>Week 8:</span> "Add Safety to LangGraph in 10 Lines" (tutorial)
      </Card>

      <Card title="About Page — Story">
        Keep it real. Solo founder from Slovakia. 15+ years in tech.<br/>
        Built KOVRIN because existing frameworks treat safety as afterthought.<br/>
        Name origin: personal (don't explain Kovalčín publicly — let it be mystery).<br/>
        Mission: "Every AI agent in production should have provable safety guarantees."
      </Card>

      <Card title="Pricing Page — Messaging">
        Lead: "Open-source core. Enterprise when you need it."<br/>
        Emphasize: OSS is NOT limited — it's the full engine.<br/>
        Pro/Enterprise = convenience (dashboard, reports, support).<br/>
        Anti-pattern: DON'T cripple free tier. That kills trust and adoption.
      </Card>
    </div>
  </div>
);

// ============== MAIN APP ==============
export default function KovrinDesignSpec() {
  const [activeTab, setActiveTab] = useState("sitemap");

  return (
    <div style={{
      background: COLORS.bg,
      color: COLORS.text,
      minHeight: "100vh",
      fontFamily: "'DM Sans', sans-serif",
    }}>
      <style>{FONT_IMPORT}</style>

      {/* Header */}
      <div style={{
        borderBottom: `1px solid ${COLORS.border}`,
        padding: "16px 24px",
        display: "flex",
        justifyContent: "space-between",
        alignItems: "center",
      }}>
        <div style={{ display: "flex", alignItems: "center", gap: "12px" }}>
          <span style={{
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: "16px",
            fontWeight: 700,
            color: COLORS.accent,
          }}>◆ KOVRIN</span>
          <span style={{
            fontFamily: "'JetBrains Mono', monospace",
            fontSize: "11px",
            color: COLORS.textDim,
          }}>Design Specification v1.0</span>
        </div>
        <span style={{
          fontFamily: "'JetBrains Mono', monospace",
          fontSize: "10px",
          color: COLORS.textDim,
          padding: "4px 10px",
          border: `1px solid ${COLORS.border}`,
        }}>FEB 2026</span>
      </div>

      {/* Tabs */}
      <div style={{
        borderBottom: `1px solid ${COLORS.border}`,
        padding: "12px 24px",
        display: "flex",
        gap: "4px",
      }}>
        {[
          ["sitemap", "Sitemap", "17"],
          ["design", "Design System", null],
          ["wireframes", "Wireframes", "4"],
          ["content", "Content", null],
        ].map(([id, label, count]) => (
          <Tab key={id} active={activeTab === id} onClick={() => setActiveTab(id)} count={count}>
            {label}
          </Tab>
        ))}
      </div>

      {/* Content */}
      <div style={{ padding: "24px", maxWidth: "900px" }}>
        {activeTab === "sitemap" && <SitemapView />}
        {activeTab === "design" && <DesignSystemView />}
        {activeTab === "wireframes" && <WireframesView />}
        {activeTab === "content" && <ContentView />}
      </div>
    </div>
  );
}
