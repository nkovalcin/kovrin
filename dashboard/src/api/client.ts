import type {
  AgentDriftMetrics,
  AutonomyProfile,
  AutonomySettings,
  CounterfactualResult,
  DelegationToken,
  ExecutionResult,
  PipelineStatus,
  PrmScore,
  ReplaySession,
  TopologyRecommendation,
  Trace,
  WsMessage,
} from '../types/kovrin'

const BASE = ''

export async function getStatus(): Promise<PipelineStatus> {
  const res = await fetch(`${BASE}/api/status`)
  return res.json()
}

export async function runPipeline(
  intent: string,
  constraints: string[] = [],
  context: Record<string, unknown> = {},
): Promise<{ intent_id: string; status: string }> {
  const res = await fetch(`${BASE}/api/run`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ intent, constraints, context }),
  })
  return res.json()
}

export async function getTraces(intentId: string): Promise<{ traces: Trace[]; total: number }> {
  const res = await fetch(`${BASE}/api/traces/${intentId}`)
  return res.json()
}

export async function getGraph(intentId: string): Promise<{ graph: Record<string, unknown> }> {
  const res = await fetch(`${BASE}/api/graph/${intentId}`)
  return res.json()
}

export async function getResult(intentId: string): Promise<ExecutionResult> {
  const res = await fetch(`${BASE}/api/result/${intentId}`)
  return res.json()
}

export async function getApprovals(): Promise<{ approvals: unknown[]; total: number }> {
  const res = await fetch(`${BASE}/api/approvals`)
  return res.json()
}

export async function approveTask(
  intentId: string,
  taskId: string,
  approved: boolean,
  reason: string = '',
): Promise<{ status: string }> {
  const res = await fetch(`${BASE}/api/approve/${intentId}/${taskId}`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ approved, reason }),
  })
  return res.json()
}

export async function getAutonomy(): Promise<AutonomySettings> {
  const res = await fetch(`${BASE}/api/autonomy`)
  return res.json()
}

export async function updateAutonomy(
  profile: AutonomyProfile,
  overrideMatrix: Record<string, string> = {},
): Promise<AutonomySettings> {
  const res = await fetch(`${BASE}/api/autonomy`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ profile, override_matrix: overrideMatrix }),
  })
  return res.json()
}

export async function getReplay(intentId: string): Promise<ReplaySession> {
  const res = await fetch(`${BASE}/api/replay/${intentId}`)
  return res.json()
}

export async function evaluateCounterfactual(
  intentId: string,
  profile: AutonomyProfile,
  overrideMatrix: Record<string, string> = {},
): Promise<{ intent_id: string; diffs: CounterfactualResult[]; total_changed: number }> {
  const res = await fetch(`${BASE}/api/replay/${intentId}/evaluate`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ profile, override_matrix: overrideMatrix }),
  })
  return res.json()
}

// ─── Phase 6: PRM, Tokens, Topology, Drift ───────────────────

export async function getPrmScores(intentId: string): Promise<{ scores: PrmScore[]; total: number }> {
  const res = await fetch(`${BASE}/api/prm/${intentId}`)
  return res.json()
}

export async function getActiveTokens(): Promise<{ tokens: DelegationToken[]; total: number; enabled: boolean }> {
  const res = await fetch(`${BASE}/api/tokens`)
  return res.json()
}

export async function getTopology(intentId: string): Promise<TopologyRecommendation & { intent_id: string }> {
  const res = await fetch(`${BASE}/api/topology/${intentId}`)
  return res.json()
}

export async function getDriftMetrics(): Promise<{ agents: AgentDriftMetrics[]; total: number; enabled: boolean }> {
  const res = await fetch(`${BASE}/api/drift`)
  return res.json()
}

export function connectWebSocket(onMessage: (msg: WsMessage) => void): WebSocket {
  const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:'
  const ws = new WebSocket(`${protocol}//${window.location.host}/ws`)

  ws.onmessage = (event) => {
    try {
      const msg = JSON.parse(event.data) as WsMessage
      onMessage(msg)
    } catch {
      // ignore malformed messages
    }
  }

  const interval = setInterval(() => {
    if (ws.readyState === WebSocket.OPEN) {
      ws.send(JSON.stringify({ type: 'ping' }))
    }
  }, 30000)

  ws.onclose = () => clearInterval(interval)

  return ws
}
