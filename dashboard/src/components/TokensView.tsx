import { useState, useEffect } from 'react'
import type { DelegationToken } from '../types/kovrin'
import { getActiveTokens } from '../api/client'

interface Props {}

export default function TokensView({}: Props) {
  const [tokens, setTokens] = useState<DelegationToken[]>([])
  const [enabled, setEnabled] = useState(false)
  const [loading, setLoading] = useState(false)

  const refresh = () => {
    setLoading(true)
    getActiveTokens()
      .then((r) => {
        setTokens(r.tokens || [])
        setEnabled(r.enabled)
      })
      .finally(() => setLoading(false))
  }

  useEffect(() => { refresh() }, [])

  if (!enabled) {
    return <p className="text-gray-500 text-sm">Delegation tokens are not enabled. Initialize Kovrin with <code className="text-emerald-400">enable_tokens=True</code>.</p>
  }

  if (loading) {
    return <p className="text-gray-500 text-sm">Loading tokens...</p>
  }

  return (
    <div className="space-y-4">
      <div className="flex items-center gap-3">
        <h2 className="text-lg font-semibold text-gray-200">Delegation Tokens</h2>
        <span className="text-[10px] text-gray-500 font-mono">{tokens.length} active</span>
        <button
          onClick={refresh}
          className="ml-auto text-xs bg-gray-700 hover:bg-gray-600 text-gray-300 px-2 py-1 rounded"
        >
          Refresh
        </button>
      </div>

      {tokens.length === 0 ? (
        <p className="text-gray-500 text-sm">No active tokens. Tokens are issued during multi-agent execution.</p>
      ) : (
        <div className="overflow-x-auto">
          <table className="w-full text-xs">
            <thead>
              <tr className="text-gray-500 border-b border-gray-700">
                <th className="text-left py-2 px-2 font-medium">Agent</th>
                <th className="text-left py-2 px-2 font-medium">Scope</th>
                <th className="text-left py-2 px-2 font-medium">Issued</th>
                <th className="text-left py-2 px-2 font-medium">Expires</th>
                <th className="text-right py-2 px-2 font-medium">Tasks</th>
                <th className="text-right py-2 px-2 font-medium">Status</th>
              </tr>
            </thead>
            <tbody>
              {tokens.map((t) => {
                const isExpired = new Date(t.expires_at) < new Date()
                return (
                  <tr key={t.id} className="border-b border-gray-800 hover:bg-gray-800/30">
                    <td className="py-2 px-2 text-gray-300 font-mono">{t.agent_id}</td>
                    <td className="py-2 px-2">
                      <div className="flex gap-1 flex-wrap">
                        {t.scope.allowed_risk_levels.map((r) => (
                          <span key={r} className="text-[10px] bg-gray-700 px-1 py-0.5 rounded text-gray-400">{r}</span>
                        ))}
                      </div>
                    </td>
                    <td className="py-2 px-2 text-gray-500 font-mono">
                      {new Date(t.issued_at).toLocaleTimeString()}
                    </td>
                    <td className="py-2 px-2 text-gray-500 font-mono">
                      {new Date(t.expires_at).toLocaleTimeString()}
                    </td>
                    <td className="py-2 px-2 text-right text-gray-400 font-mono">
                      {t.tasks_executed}/{t.scope.max_tasks}
                    </td>
                    <td className="py-2 px-2 text-right">
                      {t.revoked ? (
                        <span className="text-[10px] bg-red-500/20 text-red-400 px-1.5 py-0.5 rounded">REVOKED</span>
                      ) : isExpired ? (
                        <span className="text-[10px] bg-yellow-500/20 text-yellow-400 px-1.5 py-0.5 rounded">EXPIRED</span>
                      ) : (
                        <span className="text-[10px] bg-green-500/20 text-green-400 px-1.5 py-0.5 rounded">ACTIVE</span>
                      )}
                    </td>
                  </tr>
                )
              })}
            </tbody>
          </table>
        </div>
      )}

      <div className="text-[10px] text-gray-600 font-mono">
        Token ID prefix: {tokens[0]?.id.slice(0, 8) || 'N/A'}...
        {tokens[0]?.parent_token_id && ` | Parent: ${tokens[0].parent_token_id.slice(0, 8)}...`}
      </div>
    </div>
  )
}
