import { useState, useEffect, useRef } from 'react'
import type { AutonomyProfile, CounterfactualResult, ReplayFrame, ReplaySession } from '../types/kovrin'
import { getReplay, evaluateCounterfactual } from '../api/client'

const EVENT_COLORS: Record<string, string> = {
  INTENT_RECEIVED: 'border-blue-500/30',
  DECOMPOSITION: 'border-purple-500/30',
  CRITIC_PIPELINE: 'border-yellow-500/30',
  RISK_ROUTING: 'border-amber-500/30',
  EXECUTION_START: 'border-cyan-500/30',
  EXECUTION_COMPLETE: 'border-green-500/30',
  PIPELINE_COMPLETE: 'border-green-500/30',
  HUMAN_APPROVED: 'border-green-500/30',
  HUMAN_REJECTED: 'border-red-500/30',
}

interface Props {
  intentId: string | null
}

export default function ReplayViewer({ intentId }: Props) {
  const [session, setSession] = useState<ReplaySession | null>(null)
  const [currentFrame, setCurrentFrame] = useState(0)
  const [playing, setPlaying] = useState(false)
  const [loading, setLoading] = useState(false)
  const [cfProfile, setCfProfile] = useState<AutonomyProfile>('CAUTIOUS')
  const [cfResults, setCfResults] = useState<CounterfactualResult[] | null>(null)
  const [cfLoading, setCfLoading] = useState(false)
  const timerRef = useRef<number | null>(null)

  useEffect(() => {
    if (!intentId) return
    setLoading(true)
    getReplay(intentId)
      .then((s) => {
        setSession(s)
        setCurrentFrame(0)
        setCfResults(null)
      })
      .finally(() => setLoading(false))
  }, [intentId])

  useEffect(() => {
    if (playing && session) {
      timerRef.current = window.setInterval(() => {
        setCurrentFrame((prev) => {
          if (prev >= session.total_frames - 1) {
            setPlaying(false)
            return prev
          }
          return prev + 1
        })
      }, 800)
    }
    return () => {
      if (timerRef.current) clearInterval(timerRef.current)
    }
  }, [playing, session])

  const handleCounterfactual = async () => {
    if (!intentId) return
    setCfLoading(true)
    try {
      const result = await evaluateCounterfactual(intentId, cfProfile)
      setCfResults(result.diffs)
    } finally {
      setCfLoading(false)
    }
  }

  if (!intentId) {
    return <p className="text-gray-500 text-sm">Select a completed pipeline to replay its decisions.</p>
  }

  if (loading) {
    return <p className="text-gray-500 text-sm">Loading replay data...</p>
  }

  if (!session || session.total_frames === 0) {
    return <p className="text-gray-500 text-sm">No replay data available for this pipeline.</p>
  }

  const frame: ReplayFrame = session.frames[currentFrame]

  return (
    <div className="space-y-4">
      <div className="flex items-center gap-3">
        <h2 className="text-lg font-semibold text-gray-200">Decision Replay</h2>
        <span className={`text-[10px] px-2 py-0.5 rounded font-mono ${
          session.chain_valid
            ? 'bg-green-500/20 text-green-400'
            : 'bg-red-500/20 text-red-400'
        }`}>
          {session.chain_valid ? 'CHAIN VALID' : 'CHAIN BROKEN'}
        </span>
      </div>

      {/* Scrubber */}
      <div className="space-y-2">
        <input
          type="range"
          min={0}
          max={session.total_frames - 1}
          value={currentFrame}
          onChange={(e) => {
            setCurrentFrame(Number(e.target.value))
            setPlaying(false)
          }}
          className="w-full accent-blue-500"
        />
        <div className="flex items-center gap-2">
          <button
            onClick={() => setCurrentFrame(Math.max(0, currentFrame - 1))}
            disabled={currentFrame === 0}
            className="text-xs bg-gray-700 hover:bg-gray-600 text-gray-300 px-2 py-1 rounded disabled:opacity-30"
          >
            Prev
          </button>
          <button
            onClick={() => setPlaying(!playing)}
            className="text-xs bg-blue-600 hover:bg-blue-700 text-white px-3 py-1 rounded"
          >
            {playing ? 'Pause' : 'Play'}
          </button>
          <button
            onClick={() => setCurrentFrame(Math.min(session.total_frames - 1, currentFrame + 1))}
            disabled={currentFrame === session.total_frames - 1}
            className="text-xs bg-gray-700 hover:bg-gray-600 text-gray-300 px-2 py-1 rounded disabled:opacity-30"
          >
            Next
          </button>
          <span className="ml-auto text-xs text-gray-500 font-mono">
            {currentFrame + 1} / {session.total_frames}
          </span>
        </div>
      </div>

      {/* Current frame */}
      {frame && (
        <div className={`border rounded-lg px-4 py-3 bg-gray-800/50 ${
          EVENT_COLORS[frame.event_type] || 'border-gray-700'
        }`}>
          <div className="flex items-center gap-2 text-xs mb-2">
            <span className="font-mono font-semibold text-gray-300">{frame.event_type}</span>
            {frame.risk_level && (
              <span className="text-[10px] font-mono text-gray-500">[{frame.risk_level}]</span>
            )}
            {frame.l0_passed !== null && (
              <span className={`text-[10px] font-mono ${frame.l0_passed ? 'text-green-400' : 'text-red-400'}`}>
                {frame.l0_passed ? 'L0 PASS' : 'L0 FAIL'}
              </span>
            )}
            <span className="ml-auto text-gray-600 font-mono text-[10px]">
              #{frame.sequence}
            </span>
          </div>
          <p className="text-sm text-gray-300">{frame.description}</p>
          {frame.task_id && (
            <span className="text-[10px] font-mono text-gray-600 mt-1 block">{frame.task_id}</span>
          )}
          <div className="text-[10px] font-mono text-gray-600 mt-2">
            hash: {frame.hash.slice(0, 16)}...
          </div>
        </div>
      )}

      {/* Counterfactual evaluator */}
      <div className="border border-gray-700 rounded-lg p-3 space-y-2">
        <div className="text-xs text-gray-400 font-medium">What-If Analysis</div>
        <div className="flex items-center gap-2">
          <select
            value={cfProfile}
            onChange={(e) => setCfProfile(e.target.value as AutonomyProfile)}
            className="bg-gray-800 border border-gray-700 rounded px-2 py-1 text-xs text-gray-300"
          >
            <option value="DEFAULT">Default</option>
            <option value="CAUTIOUS">Cautious</option>
            <option value="AGGRESSIVE">Aggressive</option>
            <option value="LOCKED">Locked</option>
          </select>
          <button
            onClick={handleCounterfactual}
            disabled={cfLoading}
            className="text-xs bg-purple-600 hover:bg-purple-700 text-white px-3 py-1 rounded disabled:opacity-50"
          >
            {cfLoading ? 'Evaluating...' : 'Evaluate'}
          </button>
        </div>

        {cfResults && (
          <div className="space-y-1 mt-2">
            {cfResults.map((r) => (
              <div
                key={r.task_id}
                className={`flex items-center gap-2 text-[10px] font-mono px-2 py-1 rounded ${
                  r.changed ? 'bg-amber-500/10 text-amber-300' : 'text-gray-600'
                }`}
              >
                <span className="w-40 truncate">{r.task_description}</span>
                <span className={r.changed ? 'text-red-400' : ''}>{r.actual_action}</span>
                {r.changed && (
                  <>
                    <span className="text-gray-500">-&gt;</span>
                    <span className="text-green-400">{r.counterfactual_action}</span>
                  </>
                )}
              </div>
            ))}
            <div className="text-[10px] text-gray-500 mt-1">
              {cfResults.filter((r) => r.changed).length} of {cfResults.length} routing decisions would change
            </div>
          </div>
        )}
      </div>
    </div>
  )
}
