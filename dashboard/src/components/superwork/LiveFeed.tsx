import { useEffect, useRef, useState, useCallback } from 'react'
import type { TaskCompletionEvent, SuperWorkWsMessage } from '../../types/kovrin'
import { connectSuperWorkWebSocket } from '../../api/client'

interface FeedItem {
  id: string
  type: 'task_complete' | 'proposal_approved' | 'proposal_skipped' | 'connected' | 'disconnected'
  timestamp: string
  data?: TaskCompletionEvent
  proposalId?: string
}

interface Props {
  active: boolean
  onTaskComplete?: (event: TaskCompletionEvent) => void
  onProposalAction?: (type: 'approved' | 'skipped', proposalId: string) => void
}

export default function LiveFeed({ active, onTaskComplete, onProposalAction }: Props) {
  const [items, setItems] = useState<FeedItem[]>([])
  const [connected, setConnected] = useState(false)
  const wsRef = useRef<WebSocket | null>(null)
  const feedRef = useRef<HTMLDivElement>(null)

  const handleMessage = useCallback((msg: SuperWorkWsMessage) => {
    if (msg.type === 'pong') return

    const item: FeedItem = {
      id: crypto.randomUUID(),
      type: msg.type,
      timestamp: new Date().toISOString(),
      data: msg.data,
      proposalId: msg.proposal_id,
    }

    setItems((prev) => [item, ...prev].slice(0, 100))

    if (msg.type === 'task_complete' && msg.data && onTaskComplete) {
      onTaskComplete(msg.data)
    }
    if (msg.type === 'proposal_approved' && msg.proposal_id && onProposalAction) {
      onProposalAction('approved', msg.proposal_id)
    }
    if (msg.type === 'proposal_skipped' && msg.proposal_id && onProposalAction) {
      onProposalAction('skipped', msg.proposal_id)
    }
  }, [onTaskComplete, onProposalAction])

  useEffect(() => {
    if (!active) return

    try {
      const ws = connectSuperWorkWebSocket(handleMessage)
      wsRef.current = ws

      ws.onopen = () => {
        setConnected(true)
        setItems((prev) => [{
          id: crypto.randomUUID(),
          type: 'connected',
          timestamp: new Date().toISOString(),
        }, ...prev])
      }

      ws.onclose = () => {
        setConnected(false)
        setItems((prev) => [{
          id: crypto.randomUUID(),
          type: 'disconnected',
          timestamp: new Date().toISOString(),
        }, ...prev])
      }
    } catch {
      // WS not available
    }

    return () => {
      wsRef.current?.close()
      wsRef.current = null
    }
  }, [active, handleMessage])

  const TYPE_STYLES: Record<string, { label: string; color: string }> = {
    task_complete: { label: 'TASK', color: 'text-green-400' },
    proposal_approved: { label: 'APPROVED', color: 'text-blue-400' },
    proposal_skipped: { label: 'SKIPPED', color: 'text-gray-400' },
    connected: { label: 'CONNECTED', color: 'text-emerald-400' },
    disconnected: { label: 'DISCONNECTED', color: 'text-red-400' },
  }

  return (
    <div className="space-y-2">
      <div className="flex items-center justify-between">
        <h3 className="text-sm font-semibold text-gray-300">Live Feed</h3>
        <div className="flex items-center gap-2">
          <div className={`w-1.5 h-1.5 ${connected ? 'bg-green-400 animate-pulse' : 'bg-gray-600'}`} />
          <span className="text-[10px] font-mono text-gray-500">
            {connected ? 'CONNECTED' : 'DISCONNECTED'}
          </span>
        </div>
      </div>

      <div
        ref={feedRef}
        className="bg-gray-900 border border-gray-700 max-h-[400px] overflow-y-auto"
      >
        {items.length === 0 && (
          <div className="p-4 text-center">
            <p className="text-xs text-gray-600">Waiting for events...</p>
          </div>
        )}

        {items.map((item) => {
          const style = TYPE_STYLES[item.type] || { label: item.type, color: 'text-gray-400' }
          return (
            <div
              key={item.id}
              className="flex items-start gap-2 px-3 py-2 border-b border-gray-800/50 hover:bg-gray-800/30 transition-colors"
            >
              <span className="text-[10px] font-mono text-gray-600 shrink-0 pt-0.5">
                {new Date(item.timestamp).toLocaleTimeString()}
              </span>
              <span className={`text-[10px] font-mono ${style.color} shrink-0 w-16 pt-0.5`}>
                {style.label}
              </span>
              <div className="flex-1 min-w-0">
                {item.type === 'task_complete' && item.data && (
                  <>
                    <p className="text-xs text-gray-300 truncate">{item.data.completed_task}</p>
                    {item.data.files_changed && item.data.files_changed.length > 0 && (
                      <p className="text-[10px] text-gray-500 font-mono truncate">
                        {item.data.files_changed.length} file{item.data.files_changed.length !== 1 ? 's' : ''} changed
                      </p>
                    )}
                    {item.data.errors && item.data.errors.length > 0 && (
                      <p className="text-[10px] text-red-400 font-mono truncate">
                        {item.data.errors[0]}
                      </p>
                    )}
                  </>
                )}
                {(item.type === 'proposal_approved' || item.type === 'proposal_skipped') && item.proposalId && (
                  <p className="text-xs text-gray-400 font-mono truncate">{item.proposalId}</p>
                )}
                {(item.type === 'connected' || item.type === 'disconnected') && (
                  <p className="text-xs text-gray-500">WebSocket {item.type}</p>
                )}
              </div>
            </div>
          )
        })}
      </div>
    </div>
  )
}
