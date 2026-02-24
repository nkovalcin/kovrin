import { useCallback, useEffect, useState } from 'react'
import type {
  MetricsSnapshot,
  ProjectAnalysis,
  SuperWorkSession,
  TaskCompletionEvent,
  TaskProposal,
} from '../../types/kovrin'
import { getSuperWorkSession, getSuperWorkMetrics } from '../../api/client'
import SessionControl from './SessionControl'
import ProposalQueue from './ProposalQueue'
import MetricsPanel from './MetricsPanel'
import LiveFeed from './LiveFeed'

type SubTab = 'overview' | 'proposals' | 'feed'

export default function SuperWorkDashboard() {
  const [session, setSession] = useState<SuperWorkSession | null>(null)
  const [metrics, setMetrics] = useState<MetricsSnapshot | null>(null)
  const [proposals, setProposals] = useState<TaskProposal[]>([])
  const [analysis, setAnalysis] = useState<ProjectAnalysis | null>(null)
  const [subTab, setSubTab] = useState<SubTab>('overview')
  const [completionCount, setCompletionCount] = useState(0)

  // Check for existing session on mount
  useEffect(() => {
    getSuperWorkSession()
      .then((s) => {
        if (!('error' in s) || !s.error) {
          setSession(s)
        }
      })
      .catch(() => {})

    getSuperWorkMetrics()
      .then((m) => {
        if (!('error' in m)) {
          setMetrics(m)
        }
      })
      .catch(() => {})
  }, [])

  const handleTaskComplete = useCallback((event: TaskCompletionEvent) => {
    setCompletionCount((c) => c + 1)
    // Auto-refresh metrics on task complete
    getSuperWorkMetrics()
      .then((m) => {
        if (!('error' in m)) {
          setMetrics(m)
        }
      })
      .catch(() => {})
    // If there are errors, we could surface them
    if (event.errors && event.errors.length > 0) {
      // Could show a notification
    }
  }, [])

  const handleProposalAction = useCallback((_type: 'approved' | 'skipped', proposalId: string) => {
    setProposals((prev) =>
      prev.map((p) =>
        p.id === proposalId
          ? { ...p, status: (_type === 'approved' ? 'APPROVED' : 'SKIPPED') as TaskProposal['status'] }
          : p,
      ),
    )
  }, [])

  const handleProposalsChange = useCallback((newProposals: TaskProposal[], newAnalysis: ProjectAnalysis | null) => {
    setProposals(newProposals)
    setAnalysis(newAnalysis)
  }, [])

  const handleMetricsChange = useCallback((m: MetricsSnapshot) => {
    setMetrics(m)
  }, [])

  const SUB_TABS: { id: SubTab; label: string; badge?: number }[] = [
    { id: 'overview', label: 'Overview' },
    { id: 'proposals', label: 'Proposals', badge: proposals.filter((p) => p.status === 'PENDING').length },
    { id: 'feed', label: 'Live Feed', badge: completionCount },
  ]

  return (
    <div className="space-y-4">
      <div className="flex items-center justify-between">
        <div>
          <h2 className="text-lg font-bold text-gray-200">SuperWork</h2>
          <p className="text-xs text-gray-500">AI Agent Supervisor Platform</p>
        </div>
        <div className="flex gap-1">
          {SUB_TABS.map((t) => (
            <button
              key={t.id}
              onClick={() => {
                setSubTab(t.id)
                if (t.id === 'feed') setCompletionCount(0)
              }}
              className={`px-3 py-1.5 text-xs font-mono transition-colors ${
                subTab === t.id
                  ? 'bg-emerald-500/20 text-emerald-300 border border-emerald-500/30'
                  : 'text-gray-500 hover:text-gray-300 border border-gray-700'
              }`}
            >
              {t.label}
              {t.badge !== undefined && t.badge > 0 && (
                <span className="ml-1.5 bg-emerald-500/30 text-emerald-300 text-[10px] px-1.5 py-0.5">
                  {t.badge}
                </span>
              )}
            </button>
          ))}
        </div>
      </div>

      {subTab === 'overview' && (
        <div className="grid grid-cols-1 lg:grid-cols-2 gap-4">
          <div className="space-y-4">
            <SessionControl session={session} onSessionChange={setSession} />
            <MetricsPanel metrics={metrics} onMetricsChange={handleMetricsChange} />
          </div>
          <div>
            <ProposalQueue
              proposals={proposals}
              analysis={analysis}
              onProposalsChange={handleProposalsChange}
            />
          </div>
        </div>
      )}

      {subTab === 'proposals' && (
        <ProposalQueue
          proposals={proposals}
          analysis={analysis}
          onProposalsChange={handleProposalsChange}
        />
      )}

      {subTab === 'feed' && (
        <LiveFeed
          active={!!session}
          onTaskComplete={handleTaskComplete}
          onProposalAction={handleProposalAction}
        />
      )}
    </div>
  )
}
