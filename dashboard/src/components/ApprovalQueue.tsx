import { approveTask } from '../api/client'

export interface ApprovalItem {
  intent_id: string
  task_id: string
  description: string
  risk_level: string
  speculation_tier: string
  reason: string
  proof_obligations?: { axiom_name: string; passed: boolean; evidence: string }[]
  timestamp: string
}

const RISK_STYLES: Record<string, string> = {
  LOW: 'bg-green-500/20 text-green-400',
  MEDIUM: 'bg-yellow-500/20 text-yellow-400',
  HIGH: 'bg-orange-500/20 text-orange-400',
  CRITICAL: 'bg-red-500/20 text-red-400',
}

interface Props {
  approvals: ApprovalItem[]
  onResolved: (intentId: string, taskId: string) => void
}

export default function ApprovalQueue({ approvals, onResolved }: Props) {
  const handleAction = async (item: ApprovalItem, approved: boolean) => {
    try {
      await approveTask(item.intent_id, item.task_id, approved)
      onResolved(item.intent_id, item.task_id)
    } catch {
      // API error
    }
  }

  if (approvals.length === 0) {
    return (
      <div className="space-y-3">
        <h2 className="text-lg font-semibold text-gray-200">Approvals</h2>
        <p className="text-gray-500 text-sm">No pending approvals. High-risk tasks will appear here for review.</p>
      </div>
    )
  }

  return (
    <div className="space-y-3">
      <div className="flex items-center gap-3">
        <h2 className="text-lg font-semibold text-gray-200">Approvals</h2>
        <span className="text-xs bg-amber-500/20 text-amber-400 px-2 py-0.5 rounded font-medium">
          {approvals.length} pending
        </span>
      </div>

      <div className="space-y-3">
        {approvals.map((item) => {
          const riskStyle = RISK_STYLES[item.risk_level] || RISK_STYLES.MEDIUM
          return (
            <div
              key={`${item.intent_id}:${item.task_id}`}
              className="bg-gray-800 border border-gray-700 rounded-lg p-4 space-y-3"
            >
              <div className="flex items-start justify-between gap-3">
                <div className="flex-1 min-w-0">
                  <p className="text-sm text-gray-200 font-medium">{item.description}</p>
                  <p className="text-xs text-gray-500 mt-1 font-mono">{item.reason}</p>
                </div>
                <div className="flex items-center gap-2 shrink-0">
                  <span className={`text-[10px] px-2 py-0.5 rounded font-semibold ${riskStyle}`}>
                    {item.risk_level}
                  </span>
                  <span className="text-[10px] px-2 py-0.5 rounded bg-gray-700 text-gray-400 font-mono">
                    {item.speculation_tier}
                  </span>
                </div>
              </div>

              {item.proof_obligations && item.proof_obligations.length > 0 && (
                <div className="border-t border-gray-700 pt-2">
                  <p className="text-[10px] text-gray-500 mb-1 uppercase tracking-wide">Proof Obligations</p>
                  <div className="space-y-1">
                    {item.proof_obligations.map((po, i) => (
                      <div key={i} className="flex items-center gap-2 text-xs">
                        <span className={po.passed ? 'text-green-400' : 'text-red-400'}>
                          {po.passed ? '+' : 'x'}
                        </span>
                        <span className="text-gray-400">{po.axiom_name}</span>
                        {po.evidence && (
                          <span className="text-gray-600 truncate">{po.evidence}</span>
                        )}
                      </div>
                    ))}
                  </div>
                </div>
              )}

              <div className="flex items-center gap-2 pt-1">
                <button
                  onClick={() => handleAction(item, true)}
                  className="px-3 py-1.5 bg-green-600 hover:bg-green-500 text-white text-xs font-medium rounded-lg transition-colors"
                >
                  Approve
                </button>
                <button
                  onClick={() => handleAction(item, false)}
                  className="px-3 py-1.5 bg-red-600 hover:bg-red-500 text-white text-xs font-medium rounded-lg transition-colors"
                >
                  Reject
                </button>
                <span className="ml-auto text-[10px] text-gray-600 font-mono">
                  {new Date(item.timestamp).toLocaleTimeString()}
                </span>
              </div>
            </div>
          )
        })}
      </div>
    </div>
  )
}
