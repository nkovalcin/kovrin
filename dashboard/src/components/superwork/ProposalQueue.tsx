import { useState } from 'react'
import type { TaskProposal, ProjectAnalysis } from '../../types/kovrin'
import {
  getSuperWorkProposals,
  approveSuperWorkProposal,
  skipSuperWorkProposal,
} from '../../api/client'

interface Props {
  proposals: TaskProposal[]
  analysis: ProjectAnalysis | null
  onProposalsChange: (proposals: TaskProposal[], analysis: ProjectAnalysis | null) => void
}

const RISK_COLORS: Record<string, string> = {
  LOW: 'text-green-400 bg-green-400/10 border-green-400/20',
  MEDIUM: 'text-amber-400 bg-amber-400/10 border-amber-400/20',
  HIGH: 'text-orange-400 bg-orange-400/10 border-orange-400/20',
  CRITICAL: 'text-red-400 bg-red-400/10 border-red-400/20',
}

const STATUS_COLORS: Record<string, string> = {
  PENDING: 'text-gray-400 bg-gray-400/10',
  APPROVED: 'text-green-400 bg-green-400/10',
  SKIPPED: 'text-gray-500 bg-gray-500/10',
  EXECUTING: 'text-blue-400 bg-blue-400/10 animate-pulse',
  COMPLETED: 'text-green-400 bg-green-400/10',
  FAILED: 'text-red-400 bg-red-400/10',
}

export default function ProposalQueue({ proposals, analysis, onProposalsChange }: Props) {
  const [loading, setLoading] = useState(false)
  const [actionLoading, setActionLoading] = useState<string | null>(null)

  const handleAnalyze = async () => {
    setLoading(true)
    try {
      const result = await getSuperWorkProposals()
      onProposalsChange(result.proposals || [], result)
    } catch {
      // error
    } finally {
      setLoading(false)
    }
  }

  const handleApprove = async (id: string) => {
    setActionLoading(id)
    try {
      await approveSuperWorkProposal(id)
      onProposalsChange(
        proposals.map((p) => (p.id === id ? { ...p, status: 'APPROVED' as const } : p)),
        analysis,
      )
    } catch {
      // error
    } finally {
      setActionLoading(null)
    }
  }

  const handleSkip = async (id: string) => {
    setActionLoading(id)
    try {
      await skipSuperWorkProposal(id)
      onProposalsChange(
        proposals.map((p) => (p.id === id ? { ...p, status: 'SKIPPED' as const } : p)),
        analysis,
      )
    } catch {
      // error
    } finally {
      setActionLoading(null)
    }
  }

  return (
    <div className="space-y-3">
      <div className="flex items-center justify-between">
        <h3 className="text-sm font-semibold text-gray-300">Proposals</h3>
        <button
          onClick={handleAnalyze}
          disabled={loading}
          className="text-xs font-mono bg-emerald-500/20 text-emerald-300 hover:bg-emerald-500/30 px-3 py-1.5 border border-emerald-500/30 transition-colors disabled:opacity-40"
        >
          {loading ? 'ANALYZING...' : 'ANALYZE'}
        </button>
      </div>

      {analysis && (
        <div className="bg-gray-800/50 border border-gray-700 p-3">
          <p className="text-sm text-gray-300">{analysis.summary}</p>
          {analysis.focus_area && (
            <p className="text-xs text-gray-500 mt-1">
              Focus: <span className="text-emerald-400">{analysis.focus_area}</span>
            </p>
          )}
        </div>
      )}

      {proposals.length === 0 && !loading && (
        <div className="text-center py-8">
          <p className="text-sm text-gray-500">No proposals yet.</p>
          <p className="text-xs text-gray-600 mt-1">Click ANALYZE to generate task proposals.</p>
        </div>
      )}

      <div className="space-y-2">
        {proposals.map((proposal) => (
          <div
            key={proposal.id}
            className="bg-gray-800/50 border border-gray-700 p-3 space-y-2"
          >
            <div className="flex items-start justify-between gap-2">
              <div className="flex-1 min-w-0">
                <div className="flex items-center gap-2">
                  {proposal.priority !== undefined && (
                    <span className="text-[10px] font-mono text-gray-500">#{proposal.priority}</span>
                  )}
                  <h4 className="text-sm font-medium text-gray-200 truncate">
                    {proposal.title}
                  </h4>
                </div>
                <p className="text-xs text-gray-400 mt-1 line-clamp-2">{proposal.description}</p>
                {proposal.rationale && (
                  <p className="text-[10px] text-gray-500 mt-1 italic">{proposal.rationale}</p>
                )}
              </div>
              <div className="flex flex-col items-end gap-1 shrink-0">
                {proposal.risk_level && (
                  <span className={`text-[10px] font-mono px-1.5 py-0.5 border ${RISK_COLORS[proposal.risk_level] || 'text-gray-400'}`}>
                    {proposal.risk_level}
                  </span>
                )}
                <span className={`text-[10px] font-mono px-1.5 py-0.5 ${STATUS_COLORS[proposal.status] || 'text-gray-400'}`}>
                  {proposal.status}
                </span>
              </div>
            </div>

            <div className="flex items-center justify-between text-[10px] text-gray-500 font-mono">
              <div className="flex gap-3">
                {proposal.estimated_tokens !== undefined && (
                  <span>{proposal.estimated_tokens.toLocaleString()} tokens</span>
                )}
                {proposal.auto_execute && (
                  <span className="text-amber-400">AUTO-EXEC</span>
                )}
              </div>

              {proposal.status === 'PENDING' && (
                <div className="flex gap-1">
                  <button
                    onClick={() => handleApprove(proposal.id)}
                    disabled={actionLoading === proposal.id}
                    className="bg-green-500/20 text-green-300 hover:bg-green-500/30 px-2.5 py-1 border border-green-500/30 transition-colors disabled:opacity-40"
                  >
                    APPROVE
                  </button>
                  <button
                    onClick={() => handleSkip(proposal.id)}
                    disabled={actionLoading === proposal.id}
                    className="bg-gray-700/50 text-gray-400 hover:bg-gray-700 px-2.5 py-1 border border-gray-600 transition-colors disabled:opacity-40"
                  >
                    SKIP
                  </button>
                </div>
              )}
            </div>
          </div>
        ))}
      </div>
    </div>
  )
}
