import type { SubTask, ViewMode } from '../types/kovrin'

const STATUS_STYLES: Record<string, string> = {
  COMPLETED: 'bg-green-500/20 border-green-500/40 text-green-300',
  FAILED: 'bg-red-500/20 border-red-500/40 text-red-300',
  REJECTED_BY_L0: 'bg-red-500/20 border-red-500/40 text-red-300',
  EXECUTING: 'bg-blue-500/20 border-blue-500/40 text-blue-300',
  PENDING: 'bg-gray-500/20 border-gray-500/40 text-gray-400',
  READY: 'bg-cyan-500/20 border-cyan-500/40 text-cyan-300',
  SKIPPED: 'bg-gray-600/20 border-gray-600/40 text-gray-500',
  AWAITING_HUMAN: 'bg-amber-500/20 border-amber-500/40 text-amber-300',
}

const RISK_DOT: Record<string, string> = {
  LOW: 'bg-green-400',
  MEDIUM: 'bg-yellow-400',
  HIGH: 'bg-orange-400',
  CRITICAL: 'bg-red-400',
}

interface Props {
  tasks: SubTask[]
  rejectedTasks: SubTask[]
  graphSummary: Record<string, unknown>
  viewMode: ViewMode
}

export default function GraphView({ tasks, rejectedTasks, graphSummary, viewMode }: Props) {
  const allTasks = [...tasks, ...rejectedTasks]

  if (allTasks.length === 0) {
    return <p className="text-gray-500 text-sm">No graph data. Run a pipeline to see the execution graph.</p>
  }

  const waves = (graphSummary?.execution_order as string[][] | undefined) || []

  return (
    <div className="space-y-4">
      <h2 className="text-lg font-semibold text-gray-200">
        Execution Graph{' '}
        <span className="text-gray-500 text-sm font-normal">
          ({viewMode === 'OPERATOR' ? `${tasks.filter((t) => t.risk_level !== 'LOW').length} notable` : `${allTasks.length}`} tasks)
        </span>
      </h2>

      {waves.length > 0 && (
        <div className="space-y-3">
          {waves.map((wave, wi) => {
            const waveTasks = wave
              .map((taskId) => allTasks.find((t) => t.id === taskId))
              .filter((t): t is SubTask => t != null)
              .filter((t) => viewMode !== 'OPERATOR' || t.risk_level !== 'LOW')

            if (waveTasks.length === 0) return null

            return (
              <div key={wi}>
                <div className="text-xs text-gray-500 mb-1.5 font-mono">Wave {wi + 1}</div>
                <div className="flex flex-wrap gap-2">
                  {waveTasks.map((task) => {
                    const style = STATUS_STYLES[task.status] || STATUS_STYLES.PENDING
                    return (
                      <div key={task.id} className={`border rounded-lg px-3 py-2 max-w-xs ${style}`}>
                        <div className="flex items-center gap-2">
                          <span className={`w-2 h-2 rounded-full ${RISK_DOT[task.risk_level] || 'bg-gray-400'}`} />
                          <span className="text-xs font-mono">{task.status}</span>
                          {viewMode === 'DEVELOPER' && (
                            <span className="text-[10px] font-mono text-gray-500">{task.speculation_tier}</span>
                          )}
                        </div>
                        <p className="text-sm mt-1">{task.description}</p>
                        {viewMode !== 'OPERATOR' && task.dependencies.length > 0 && (
                          <div className="text-[10px] text-gray-500 mt-1 font-mono">
                            deps: {task.dependencies.join(', ')}
                          </div>
                        )}
                        {viewMode === 'DEVELOPER' && task.output && (
                          <div className="text-[10px] text-gray-500 mt-1 max-h-20 overflow-y-auto bg-black/20 rounded px-2 py-1">
                            {task.output.slice(0, 200)}
                          </div>
                        )}
                      </div>
                    )
                  })}
                </div>
              </div>
            )
          })}
        </div>
      )}

      {rejectedTasks.length > 0 && (
        <div>
          <div className="text-xs text-red-400 mb-1.5 font-mono">Rejected by Critics</div>
          <div className="flex flex-wrap gap-2">
            {rejectedTasks.map((task) => (
              <div key={task.id} className="border rounded-lg px-3 py-2 max-w-xs bg-red-500/10 border-red-500/30 text-red-300">
                <div className="flex items-center gap-2">
                  <span className={`w-2 h-2 rounded-full ${RISK_DOT[task.risk_level] || 'bg-gray-400'}`} />
                  <span className="text-xs font-mono">REJECTED</span>
                </div>
                <p className="text-sm mt-1">{task.description}</p>
              </div>
            ))}
          </div>
        </div>
      )}
    </div>
  )
}
