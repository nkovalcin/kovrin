import { useState } from 'react'
import type { SuperWorkSession } from '../../types/kovrin'
import { startSuperWorkSession, getSuperWorkSession } from '../../api/client'

interface Props {
  session: SuperWorkSession | null
  onSessionChange: (session: SuperWorkSession | null) => void
}

export default function SessionControl({ session, onSessionChange }: Props) {
  const [projectPath, setProjectPath] = useState('')
  const [loading, setLoading] = useState(false)
  const [error, setError] = useState<string | null>(null)

  const handleStart = async () => {
    if (!projectPath.trim()) return
    setLoading(true)
    setError(null)
    try {
      const s = await startSuperWorkSession(projectPath.trim())
      onSessionChange(s)
    } catch (e) {
      setError(e instanceof Error ? e.message : 'Failed to start session')
    } finally {
      setLoading(false)
    }
  }

  const handleRefresh = async () => {
    setLoading(true)
    try {
      const s = await getSuperWorkSession()
      if ('error' in s && s.error) {
        onSessionChange(null)
      } else {
        onSessionChange(s)
      }
    } catch {
      onSessionChange(null)
    } finally {
      setLoading(false)
    }
  }

  if (session) {
    return (
      <div className="bg-gray-800/50 border border-gray-700 p-4">
        <div className="flex items-center justify-between mb-3">
          <div className="flex items-center gap-2">
            <div className={`w-2 h-2 ${
              session.status === 'WATCHING' ? 'bg-green-400 animate-pulse' :
              session.status === 'PAUSED' ? 'bg-amber-400' :
              session.status === 'STOPPED' ? 'bg-red-400' :
              'bg-gray-400 animate-pulse'
            }`} />
            <span className="text-sm font-mono text-gray-300">{session.status}</span>
          </div>
          <button
            onClick={handleRefresh}
            disabled={loading}
            className="text-xs text-gray-500 hover:text-gray-300 font-mono"
          >
            {loading ? '...' : 'REFRESH'}
          </button>
        </div>
        <div className="space-y-1 text-xs">
          <div className="flex justify-between">
            <span className="text-gray-500">Session</span>
            <span className="text-gray-400 font-mono">{session.id.slice(0, 12)}...</span>
          </div>
          <div className="flex justify-between">
            <span className="text-gray-500">Project</span>
            <span className="text-gray-400 font-mono truncate ml-4 max-w-[200px]">{session.project_path}</span>
          </div>
          <div className="flex justify-between">
            <span className="text-gray-500">Started</span>
            <span className="text-gray-400 font-mono">
              {new Date(session.started_at).toLocaleTimeString()}
            </span>
          </div>
        </div>
      </div>
    )
  }

  return (
    <div className="bg-gray-800/50 border border-gray-700 p-4">
      <h3 className="text-sm font-semibold text-gray-300 mb-3">Start Session</h3>
      <div className="space-y-2">
        <input
          type="text"
          value={projectPath}
          onChange={(e) => setProjectPath(e.target.value)}
          placeholder="/path/to/project"
          className="w-full bg-gray-900 border border-gray-700 px-3 py-2 text-sm font-mono text-gray-300 placeholder:text-gray-600 focus:outline-none focus:border-emerald-500"
        />
        {error && <p className="text-xs text-red-400">{error}</p>}
        <div className="flex gap-2">
          <button
            onClick={handleStart}
            disabled={loading || !projectPath.trim()}
            className="flex-1 bg-emerald-500 hover:bg-emerald-600 disabled:opacity-40 disabled:cursor-not-allowed text-white text-sm font-mono py-2 px-4 transition-colors"
          >
            {loading ? 'STARTING...' : 'START'}
          </button>
          <button
            onClick={handleRefresh}
            disabled={loading}
            className="text-xs text-gray-500 hover:text-gray-300 border border-gray-700 px-3 font-mono"
          >
            CHECK
          </button>
        </div>
      </div>
    </div>
  )
}
