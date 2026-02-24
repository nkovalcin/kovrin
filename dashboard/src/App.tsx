import { useCallback, useEffect, useRef, useState } from 'react'
import IntentPanel from './components/IntentPanel'
import TraceViewer from './components/TraceViewer'
import GraphView from './components/GraphView'
import WatchdogStatus from './components/WatchdogStatus'
import ResultPanel from './components/ResultPanel'
import ApprovalQueue from './components/ApprovalQueue'
import ViewModeSelector from './components/ViewModeSelector'
import AutonomyControls from './components/AutonomyControls'
import ReplayViewer from './components/ReplayViewer'
import PrmScoreView from './components/PrmScoreView'
import TokensView from './components/TokensView'
import TopologyView from './components/TopologyView'
import SuperWorkDashboard from './components/superwork/SuperWorkDashboard'
import type { ApprovalItem } from './components/ApprovalQueue'
import { connectWebSocket, getAutonomy, getResult, getStatus, runPipeline } from './api/client'
import type {
  AutonomySettings,
  ExecutionResult,
  PipelineStatus,
  Trace,
  ViewMode,
  WatchdogAlert,
  WsMessage,
} from './types/kovrin'

type Tab = 'superwork' | 'intent' | 'traces' | 'graph' | 'watchdog' | 'result' | 'approvals' | 'autonomy' | 'replay' | 'prm' | 'tokens'

const TABS: { id: Tab; label: string; section?: string }[] = [
  { id: 'superwork', label: 'SuperWork', section: 'supervisor' },
  { id: 'intent', label: 'Intent', section: 'pipeline' },
  { id: 'traces', label: 'Traces', section: 'pipeline' },
  { id: 'graph', label: 'Graph', section: 'pipeline' },
  { id: 'prm', label: 'PRM', section: 'pipeline' },
  { id: 'tokens', label: 'Tokens', section: 'pipeline' },
  { id: 'watchdog', label: 'Watchdog', section: 'safety' },
  { id: 'approvals', label: 'Approvals', section: 'safety' },
  { id: 'autonomy', label: 'Autonomy', section: 'safety' },
  { id: 'replay', label: 'Replay', section: 'pipeline' },
  { id: 'result', label: 'Result', section: 'pipeline' },
]

const DEFAULT_AUTONOMY: AutonomySettings = {
  profile: 'DEFAULT',
  override_matrix: {},
  updated_at: new Date().toISOString(),
}

export default function App() {
  const [tab, setTab] = useState<Tab>('superwork')
  const [isRunning, setIsRunning] = useState(false)
  const [status, setStatus] = useState<PipelineStatus | null>(null)
  const [result, setResult] = useState<ExecutionResult | null>(null)
  const [traces, setTraces] = useState<Trace[]>([])
  const [alerts, setAlerts] = useState<WatchdogAlert[]>([])
  const [watchdogState, setWatchdogState] = useState<'ok' | 'warn' | 'paused' | 'killed'>('ok')
  const [approvals, setApprovals] = useState<ApprovalItem[]>([])
  const [viewMode, setViewMode] = useState<ViewMode>('ANALYST')
  const [autonomySettings, setAutonomySettings] = useState<AutonomySettings>(DEFAULT_AUTONOMY)
  const [currentIntentId, setCurrentIntentId] = useState<string | null>(null)
  const wsRef = useRef<WebSocket | null>(null)

  useEffect(() => {
    getStatus().then(setStatus).catch(() => {})
    getAutonomy().then(setAutonomySettings).catch(() => {})
  }, [])

  const handleWsMessage = useCallback((msg: WsMessage) => {
    if (msg.type === 'trace' && msg.data) {
      const trace = msg.data as unknown as Trace
      setTraces((prev) => [...prev, trace])

      if (trace.event_type?.startsWith('WATCHDOG_')) {
        const alert: WatchdogAlert = {
          id: trace.id,
          timestamp: trace.timestamp,
          severity: trace.event_type.replace('WATCHDOG_', '') as WatchdogAlert['severity'],
          reason: trace.description,
          task_id: trace.task_id,
          intent_id: trace.intent_id,
          rule: (trace.details?.rule as string) || '',
        }
        setAlerts((prev) => {
          const next = [...prev, alert]
          if (next.some((a) => a.severity === 'KILL')) setWatchdogState('killed')
          else if (next.some((a) => a.severity === 'PAUSE')) setWatchdogState('paused')
          else if (next.length > 0) setWatchdogState('warn')
          return next
        })
      }
    }

    if (msg.type === 'approval_request' && msg.data) {
      const item = msg.data as unknown as ApprovalItem
      setApprovals((prev) => [...prev, item])
      setTab('approvals')
    }

    if (msg.type === 'autonomy_updated' && msg.data) {
      setAutonomySettings(msg.data as unknown as AutonomySettings)
    }

    if (msg.type === 'pipeline_complete' && msg.intent_id) {
      setIsRunning(false)
      setCurrentIntentId(msg.intent_id)
      getResult(msg.intent_id).then((r) => {
        setResult(r)
        if (r.traces && r.traces.length > 0) {
          setTraces(r.traces)
        }
      }).catch(() => {})
      getStatus().then(setStatus).catch(() => {})
    }
  }, [])

  useEffect(() => {
    try {
      wsRef.current = connectWebSocket(handleWsMessage)
    } catch {
      // WebSocket not available
    }
    return () => wsRef.current?.close()
  }, [handleWsMessage])

  const handleRun = async (intent: string, constraints: string[], context: Record<string, unknown>) => {
    setIsRunning(true)
    setResult(null)
    setTraces([])
    setAlerts([])
    setApprovals([])
    setWatchdogState('ok')
    setCurrentIntentId(null)
    try {
      const res = await runPipeline(intent, constraints, context)
      setCurrentIntentId(res.intent_id)
      const poll = setInterval(async () => {
        try {
          const r = await getResult(res.intent_id)
          if (r && r.output) {
            clearInterval(poll)
            setResult(r)
            setTraces(r.traces || [])
            setIsRunning(false)
            setTab('traces')
            getStatus().then(setStatus).catch(() => {})
          }
        } catch {
          // still running
        }
      }, 2000)
      setTimeout(() => {
        clearInterval(poll)
        setIsRunning(false)
      }, 120000)
    } catch {
      setIsRunning(false)
    }
  }

  const handleApprovalResolved = (intentId: string, taskId: string) => {
    setApprovals((prev) =>
      prev.filter((a) => !(a.intent_id === intentId && a.task_id === taskId))
    )
  }

  return (
    <div className="min-h-screen flex">
      <nav className="w-48 bg-[#111113] border-r border-[#27272A] p-4 flex flex-col">
        <div className="mb-4">
          <h1 className="text-xl font-bold text-emerald-400 tracking-tight">KOVRIN</h1>
          <p className="text-[10px] text-gray-500 mt-0.5 font-mono">v{status?.version || '2.0.0-alpha'}</p>
        </div>

        <div className="mb-4">
          <ViewModeSelector viewMode={viewMode} onChange={setViewMode} />
        </div>

        <div className="space-y-1">
          {(() => {
            let lastSection = ''
            return TABS.map((t) => {
              const showSection = t.section && t.section !== lastSection
              if (t.section) lastSection = t.section
              return (
                <div key={t.id}>
                  {showSection && (
                    <p className="text-[9px] uppercase tracking-widest text-gray-600 mt-3 mb-1 px-3 font-mono">
                      {t.section}
                    </p>
                  )}
                  <button
                    onClick={() => setTab(t.id)}
                    className={`w-full text-left px-3 py-2 text-sm transition-colors ${
                      tab === t.id
                        ? 'bg-emerald-500/20 text-emerald-300'
                        : 'text-[#71717A] hover:text-[#FAFAFA] hover:bg-[#18181B]'
                    }`}
                  >
                    {t.label}
                    {t.id === 'traces' && traces.length > 0 && (
                      <span className="ml-2 text-[10px] bg-gray-700 px-1.5 py-0.5">{traces.length}</span>
                    )}
                    {t.id === 'watchdog' && alerts.length > 0 && (
                      <span className="ml-2 text-[10px] bg-red-500/30 text-red-300 px-1.5 py-0.5">{alerts.length}</span>
                    )}
                    {t.id === 'approvals' && approvals.length > 0 && (
                      <span className="ml-2 text-[10px] bg-amber-500/30 text-amber-300 px-1.5 py-0.5 animate-pulse">{approvals.length}</span>
                    )}
                  </button>
                </div>
              )
            })
          })()}
        </div>

        <div className="mt-auto pt-4 border-t border-[#27272A]">
          <div className="text-[10px] text-gray-500 space-y-1">
            <div className="flex justify-between">
              <span>Running</span>
              <span className="text-gray-400">{status?.running_pipelines || 0}</span>
            </div>
            <div className="flex justify-between">
              <span>Completed</span>
              <span className="text-gray-400">{status?.completed_pipelines || 0}</span>
            </div>
          </div>
        </div>
      </nav>

      <main className="flex-1 p-6 overflow-y-auto max-h-screen">
        {tab === 'superwork' && (
          <SuperWorkDashboard />
        )}
        {tab === 'intent' && (
          <IntentPanel onSubmit={handleRun} isRunning={isRunning} />
        )}
        {tab === 'traces' && (
          <TraceViewer traces={traces} viewMode={viewMode} />
        )}
        {tab === 'graph' && result && (
          <div className="space-y-4">
            <TopologyView intentId={currentIntentId} />
            <GraphView
              tasks={result.sub_tasks}
              rejectedTasks={result.rejected_tasks}
              graphSummary={result.graph_summary}
              viewMode={viewMode}
            />
          </div>
        )}
        {tab === 'graph' && !result && (
          <p className="text-gray-500 text-sm">No graph data. Run a pipeline to see the execution graph.</p>
        )}
        {tab === 'prm' && (
          <PrmScoreView intentId={currentIntentId} />
        )}
        {tab === 'tokens' && (
          <TokensView />
        )}
        {tab === 'watchdog' && (
          <WatchdogStatus alerts={alerts} status={watchdogState} />
        )}
        {tab === 'approvals' && (
          <ApprovalQueue approvals={approvals} onResolved={handleApprovalResolved} />
        )}
        {tab === 'autonomy' && (
          <AutonomyControls settings={autonomySettings} onUpdated={setAutonomySettings} />
        )}
        {tab === 'replay' && (
          <ReplayViewer intentId={currentIntentId} />
        )}
        {tab === 'result' && result && (
          <ResultPanel output={result.output} success={result.success} />
        )}
        {tab === 'result' && !result && (
          <p className="text-gray-500 text-sm">No results yet. Run a pipeline to see output.</p>
        )}
      </main>
    </div>
  )
}
