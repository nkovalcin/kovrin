import { useState, useMemo } from 'react'
import type { Trace, ViewMode } from '../types/kovrin'

const EVENT_COLORS: Record<string, string> = {
  INTENT_RECEIVED: 'bg-blue-500/20 text-blue-300 border-blue-500/30',
  DECOMPOSITION: 'bg-purple-500/20 text-purple-300 border-purple-500/30',
  CRITIC_PIPELINE: 'bg-yellow-500/20 text-yellow-300 border-yellow-500/30',
  L0_CHECK: 'bg-yellow-500/20 text-yellow-300 border-yellow-500/30',
  RISK_ROUTING: 'bg-amber-500/20 text-amber-300 border-amber-500/30',
  EXECUTION_START: 'bg-cyan-500/20 text-cyan-300 border-cyan-500/30',
  EXECUTION_COMPLETE: 'bg-green-500/20 text-green-300 border-green-500/30',
  PIPELINE_COMPLETE: 'bg-green-500/20 text-green-300 border-green-500/30',
  PIPELINE_ABORTED: 'bg-red-500/20 text-red-300 border-red-500/30',
  AGENT_ASSIGNMENT: 'bg-indigo-500/20 text-indigo-300 border-indigo-500/30',
  AGENT_ASSIGNED: 'bg-indigo-500/20 text-indigo-300 border-indigo-500/30',
  AGENT_COMPLETED: 'bg-teal-500/20 text-teal-300 border-teal-500/30',
  WATCHDOG_WARN: 'bg-yellow-500/20 text-yellow-300 border-yellow-500/30',
  WATCHDOG_PAUSE: 'bg-orange-500/20 text-orange-300 border-orange-500/30',
  WATCHDOG_KILL: 'bg-red-500/20 text-red-300 border-red-500/30',
  GRAPH_OPTIMIZATION: 'bg-violet-500/20 text-violet-300 border-violet-500/30',
  MULTI_AGENT_MODE: 'bg-indigo-500/20 text-indigo-300 border-indigo-500/30',
  MCTS_EXPLORATION: 'bg-fuchsia-500/20 text-fuchsia-300 border-fuchsia-500/30',
  HUMAN_APPROVED: 'bg-green-500/20 text-green-300 border-green-500/30',
  HUMAN_REJECTED: 'bg-red-500/20 text-red-300 border-red-500/30',
}

const DEFAULT_COLOR = 'bg-gray-500/20 text-gray-300 border-gray-500/30'

function L0Badge({ passed }: { passed: boolean | null }) {
  if (passed === null) return null
  return passed ? (
    <span className="text-[10px] px-1.5 py-0.5 rounded bg-green-500/20 text-green-400 font-mono">L0 PASS</span>
  ) : (
    <span className="text-[10px] px-1.5 py-0.5 rounded bg-red-500/20 text-red-400 font-mono">L0 FAIL</span>
  )
}

function RiskBadge({ level }: { level: string | null }) {
  if (!level) return null
  const colors: Record<string, string> = {
    LOW: 'text-green-400',
    MEDIUM: 'text-yellow-400',
    HIGH: 'text-orange-400',
    CRITICAL: 'text-red-400',
  }
  return <span className={`text-[10px] font-mono ${colors[level] || 'text-gray-400'}`}>[{level}]</span>
}

interface TaskGroup {
  taskId: string
  traces: Trace[]
  hasErrors: boolean
}

interface Props {
  traces: Trace[]
  viewMode: ViewMode
}

export default function TraceViewer({ traces, viewMode }: Props) {
  const [expandedTasks, setExpandedTasks] = useState<Set<string>>(new Set())
  const [filterText, setFilterText] = useState('')
  const [filterEvent, setFilterEvent] = useState('')

  const filteredTraces = useMemo(() => {
    let result = traces
    if (filterText) {
      const lower = filterText.toLowerCase()
      result = result.filter(
        (t) => t.description.toLowerCase().includes(lower) || t.event_type.toLowerCase().includes(lower),
      )
    }
    if (filterEvent) {
      result = result.filter((t) => t.event_type === filterEvent)
    }
    return result
  }, [traces, filterText, filterEvent])

  const taskGroups = useMemo(() => {
    const groups = new Map<string, Trace[]>()
    for (const t of filteredTraces) {
      const key = t.task_id || '__global__'
      if (!groups.has(key)) groups.set(key, [])
      groups.get(key)!.push(t)
    }
    const result: TaskGroup[] = []
    for (const [taskId, groupTraces] of groups) {
      result.push({
        taskId,
        traces: groupTraces,
        hasErrors: groupTraces.some(
          (t) => t.event_type.includes('FAIL') || t.event_type.includes('REJECT') || t.event_type.includes('KILL'),
        ),
      })
    }
    return result
  }, [filteredTraces])

  const eventTypes = useMemo(() => {
    const types = new Set(traces.map((t) => t.event_type))
    return Array.from(types).sort()
  }, [traces])

  if (traces.length === 0) {
    return <p className="text-gray-500 text-sm">No trace events yet. Run a pipeline to see execution traces.</p>
  }

  const toggleTask = (taskId: string) => {
    setExpandedTasks((prev) => {
      const next = new Set(prev)
      if (next.has(taskId)) next.delete(taskId)
      else next.add(taskId)
      return next
    })
  }

  // OPERATOR: intent-level summary
  if (viewMode === 'OPERATOR') {
    const completed = filteredTraces.filter((t) => t.event_type === 'EXECUTION_COMPLETE').length
    const total = filteredTraces.filter((t) => t.event_type === 'EXECUTION_START').length
    const hasError = filteredTraces.some((t) => t.event_type.includes('ABORT') || t.event_type.includes('KILL'))

    return (
      <div className="space-y-3">
        <h2 className="text-lg font-semibold text-gray-200">
          Pipeline Summary
        </h2>
        <div className="grid grid-cols-3 gap-3">
          <div className="bg-gray-800 rounded-lg px-4 py-3 text-center">
            <div className="text-2xl font-bold text-gray-200">{filteredTraces.length}</div>
            <div className="text-xs text-gray-500">Events</div>
          </div>
          <div className="bg-gray-800 rounded-lg px-4 py-3 text-center">
            <div className="text-2xl font-bold text-green-400">{completed}/{total}</div>
            <div className="text-xs text-gray-500">Tasks Completed</div>
          </div>
          <div className="bg-gray-800 rounded-lg px-4 py-3 text-center">
            <div className={`text-2xl font-bold ${hasError ? 'text-red-400' : 'text-green-400'}`}>
              {hasError ? 'ERROR' : 'OK'}
            </div>
            <div className="text-xs text-gray-500">Status</div>
          </div>
        </div>
        {taskGroups
          .filter((g) => g.taskId !== '__global__')
          .map((group) => {
            const lastTrace = group.traces[group.traces.length - 1]
            return (
              <div key={group.taskId} className={`border rounded-lg px-3 py-2 ${group.hasErrors ? 'border-red-500/30 bg-red-500/10' : 'border-gray-700 bg-gray-800/50'}`}>
                <div className="flex items-center gap-2">
                  <span className="text-xs font-mono text-gray-400">{group.taskId}</span>
                  <span className="text-xs text-gray-500">{group.traces.length} events</span>
                  <span className="ml-auto text-xs text-gray-500">{lastTrace?.event_type}</span>
                </div>
              </div>
            )
          })}
      </div>
    )
  }

  // ANALYST: task-grouped with expand/collapse
  if (viewMode === 'ANALYST') {
    return (
      <div className="space-y-2">
        <div className="flex items-center gap-2 mb-3">
          <h2 className="text-lg font-semibold text-gray-200">
            Trace Log <span className="text-gray-500 text-sm font-normal">({filteredTraces.length} events)</span>
          </h2>
          <input
            type="text"
            placeholder="Filter..."
            value={filterText}
            onChange={(e) => setFilterText(e.target.value)}
            className="ml-auto bg-gray-800 border border-gray-700 rounded px-2 py-1 text-xs text-gray-300 w-40"
          />
          <select
            value={filterEvent}
            onChange={(e) => setFilterEvent(e.target.value)}
            className="bg-gray-800 border border-gray-700 rounded px-2 py-1 text-xs text-gray-300"
          >
            <option value="">All types</option>
            {eventTypes.map((t) => (
              <option key={t} value={t}>{t}</option>
            ))}
          </select>
        </div>
        {taskGroups.map((group) => {
          const isExpanded = expandedTasks.has(group.taskId)
          const label = group.taskId === '__global__' ? 'Pipeline' : group.taskId
          return (
            <div key={group.taskId} className="border border-gray-700 rounded-lg overflow-hidden">
              <button
                onClick={() => toggleTask(group.taskId)}
                className={`w-full flex items-center gap-2 px-3 py-2 text-left text-sm hover:bg-gray-700/50 ${
                  group.hasErrors ? 'bg-red-500/10' : 'bg-gray-800/50'
                }`}
              >
                <span className="text-gray-500 text-xs">{isExpanded ? '▼' : '▶'}</span>
                <span className="font-mono text-gray-300 text-xs">{label}</span>
                <span className="text-gray-500 text-xs">{group.traces.length} events</span>
              </button>
              {isExpanded && (
                <div className="border-t border-gray-700 space-y-1 p-2">
                  {group.traces.map((t, i) => {
                    const color = EVENT_COLORS[t.event_type] || DEFAULT_COLOR
                    return (
                      <div key={t.id || i} className={`border rounded-lg px-3 py-2 ${color}`}>
                        <div className="flex items-center gap-2 text-xs">
                          <span className="font-mono font-semibold">{t.event_type}</span>
                          <RiskBadge level={t.risk_level} />
                          <L0Badge passed={t.l0_passed} />
                          <span className="ml-auto text-gray-500 font-mono text-[10px]">
                            {new Date(t.timestamp).toLocaleTimeString()}
                          </span>
                        </div>
                        <p className="text-sm mt-1 opacity-90">{t.description}</p>
                      </div>
                    )
                  })}
                </div>
              )}
            </div>
          )
        })}
      </div>
    )
  }

  // DEVELOPER: flat list with full details
  return (
    <div className="space-y-1.5">
      <div className="flex items-center gap-2 mb-3">
        <h2 className="text-lg font-semibold text-gray-200">
          Trace Log <span className="text-gray-500 text-sm font-normal">({filteredTraces.length} events)</span>
        </h2>
        <input
          type="text"
          placeholder="Filter..."
          value={filterText}
          onChange={(e) => setFilterText(e.target.value)}
          className="ml-auto bg-gray-800 border border-gray-700 rounded px-2 py-1 text-xs text-gray-300 w-40"
        />
        <select
          value={filterEvent}
          onChange={(e) => setFilterEvent(e.target.value)}
          className="bg-gray-800 border border-gray-700 rounded px-2 py-1 text-xs text-gray-300"
        >
          <option value="">All types</option>
          {eventTypes.map((t) => (
            <option key={t} value={t}>{t}</option>
          ))}
        </select>
      </div>
      {filteredTraces.map((t, i) => {
        const color = EVENT_COLORS[t.event_type] || DEFAULT_COLOR
        return (
          <div key={t.id || i} className={`border rounded-lg px-3 py-2 ${color}`}>
            <div className="flex items-center gap-2 text-xs">
              <span className="font-mono font-semibold">{t.event_type}</span>
              <RiskBadge level={t.risk_level} />
              <L0Badge passed={t.l0_passed} />
              <span className="ml-auto text-gray-500 font-mono text-[10px]">
                {new Date(t.timestamp).toLocaleTimeString()}
              </span>
            </div>
            <p className="text-sm mt-1 opacity-90">{t.description}</p>
            {t.task_id && (
              <span className="text-[10px] font-mono text-gray-500 mt-0.5 block">{t.task_id}</span>
            )}
            {t.details && Object.keys(t.details).length > 0 && (
              <pre className="text-[10px] font-mono text-gray-500 mt-1 bg-black/20 rounded px-2 py-1 overflow-x-auto">
                {JSON.stringify(t.details, null, 2)}
              </pre>
            )}
          </div>
        )
      })}
    </div>
  )
}
