import { useState, useEffect } from 'react'
import type { AgentDriftMetrics, WatchdogAlert } from '../types/kovrin'
import { getDriftMetrics } from '../api/client'

const SEVERITY_STYLES: Record<string, string> = {
  WARN: 'bg-yellow-500/20 border-yellow-500/30 text-yellow-300',
  PAUSE: 'bg-orange-500/20 border-orange-500/30 text-orange-300',
  KILL: 'bg-red-500/20 border-red-500/30 text-red-300',
}

const STATUS_DOT: Record<string, string> = {
  ok: 'bg-green-400',
  warn: 'bg-yellow-400',
  paused: 'bg-orange-400',
  killed: 'bg-red-400',
}

interface Props {
  alerts: WatchdogAlert[]
  status: 'ok' | 'warn' | 'paused' | 'killed'
}

const DRIFT_COLORS: Record<string, string> = {
  NONE: 'text-green-400',
  LOW: 'text-yellow-400',
  MODERATE: 'text-orange-400',
  HIGH: 'text-red-400',
  CRITICAL: 'text-red-500 font-bold',
}

export default function WatchdogStatus({ alerts, status }: Props) {
  const [driftMetrics, setDriftMetrics] = useState<AgentDriftMetrics[]>([])
  const [driftEnabled, setDriftEnabled] = useState(false)

  useEffect(() => {
    getDriftMetrics()
      .then((r) => {
        setDriftMetrics(r.agents || [])
        setDriftEnabled(r.enabled)
      })
      .catch(() => {})
  }, [])

  return (
    <div className="space-y-3">
      <div className="flex items-center gap-3">
        <h2 className="text-lg font-semibold text-gray-200">Watchdog</h2>
        <span className="flex items-center gap-1.5 text-sm text-gray-400">
          <span className={`w-2.5 h-2.5 rounded-full ${STATUS_DOT[status]} animate-pulse`} />
          {status.toUpperCase()}
        </span>
      </div>

      {alerts.length === 0 ? (
        <p className="text-gray-500 text-sm">No alerts. Watchdog is monitoring execution.</p>
      ) : (
        <div className="space-y-1.5">
          {alerts.map((a) => {
            const style = SEVERITY_STYLES[a.severity] || SEVERITY_STYLES.WARN
            return (
              <div key={a.id} className={`border rounded-lg px-3 py-2 ${style}`}>
                <div className="flex items-center gap-2 text-xs">
                  <span className="font-semibold">{a.severity}</span>
                  <span className="font-mono text-gray-400">{a.rule}</span>
                  <span className="ml-auto text-gray-500 font-mono text-[10px]">
                    {new Date(a.timestamp).toLocaleTimeString()}
                  </span>
                </div>
                <p className="text-sm mt-1">{a.reason}</p>
              </div>
            )
          })}
        </div>
      )}

      {/* Agent Drift Metrics */}
      {driftEnabled && driftMetrics.length > 0 && (
        <div className="border border-gray-700 rounded-lg p-3 space-y-2 mt-4">
          <div className="text-xs text-gray-400 font-medium">Agent Drift Detection</div>
          <div className="space-y-1">
            {driftMetrics.map((m) => (
              <div key={m.agent_name} className="flex items-center gap-3 text-[10px] font-mono">
                <span className="text-gray-300 w-28 truncate">{m.agent_name}</span>
                <span className={DRIFT_COLORS[m.drift_level] || 'text-gray-500'}>{m.drift_level}</span>
                <span className="text-gray-500">prm={m.average_prm_score.toFixed(2)}</span>
                <span className="text-gray-500">success={Math.round(m.success_rate * 100)}%</span>
                <span className="text-gray-600 ml-auto">{m.total_executions} runs</span>
              </div>
            ))}
          </div>
        </div>
      )}
    </div>
  )
}
