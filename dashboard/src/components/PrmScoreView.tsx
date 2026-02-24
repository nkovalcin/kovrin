import { useState, useEffect } from 'react'
import type { PrmScore } from '../types/kovrin'
import { getPrmScores } from '../api/client'

const scoreColor = (score: number) => {
  if (score >= 0.7) return 'text-green-400'
  if (score >= 0.4) return 'text-yellow-400'
  return 'text-red-400'
}

const scoreBg = (score: number) => {
  if (score >= 0.7) return 'bg-green-500/20'
  if (score >= 0.4) return 'bg-yellow-500/20'
  return 'bg-red-500/20'
}

interface Props {
  intentId: string | null
}

export default function PrmScoreView({ intentId }: Props) {
  const [scores, setScores] = useState<PrmScore[]>([])
  const [loading, setLoading] = useState(false)
  const [expanded, setExpanded] = useState<string | null>(null)

  useEffect(() => {
    if (!intentId) return
    setLoading(true)
    getPrmScores(intentId)
      .then((r) => setScores(r.scores || []))
      .finally(() => setLoading(false))
  }, [intentId])

  if (!intentId) {
    return <p className="text-gray-500 text-sm">Run a pipeline with PRM enabled to see step-level scores.</p>
  }

  if (loading) {
    return <p className="text-gray-500 text-sm">Loading PRM scores...</p>
  }

  if (scores.length === 0) {
    return <p className="text-gray-500 text-sm">No PRM data. Enable PRM to see step-level quality scores.</p>
  }

  return (
    <div className="space-y-4">
      <div className="flex items-center gap-3">
        <h2 className="text-lg font-semibold text-gray-200">Process Reward Model</h2>
        <span className="text-[10px] text-gray-500 font-mono">{scores.length} tasks scored</span>
      </div>

      <div className="space-y-2">
        {scores.map((score) => (
          <div key={score.task_id} className="border border-gray-700 rounded-lg overflow-hidden">
            <button
              onClick={() => setExpanded(expanded === score.task_id ? null : score.task_id)}
              className="w-full flex items-center gap-3 px-4 py-3 hover:bg-gray-800/50 transition-colors"
            >
              <span className={`text-sm font-mono font-bold ${scoreColor(score.aggregate_score)}`}>
                {score.aggregate_score.toFixed(2)}
              </span>
              <div className="flex-1 h-1.5 bg-gray-800 rounded-full overflow-hidden">
                <div
                  className={`h-full rounded-full transition-all ${scoreBg(score.aggregate_score)}`}
                  style={{ width: `${score.aggregate_score * 100}%` }}
                />
              </div>
              <span className="text-[10px] text-gray-500 font-mono">{score.step_scores.length} steps</span>
              <span className="text-[10px] text-gray-600 font-mono truncate max-w-[200px]">{score.task_id}</span>
              <span className="text-gray-600 text-xs">{expanded === score.task_id ? '\u25B2' : '\u25BC'}</span>
            </button>

            {expanded === score.task_id && (
              <div className="border-t border-gray-700/50 px-4 py-3 space-y-2 bg-gray-800/30">
                {score.step_scores.map((step, i) => (
                  <div key={i} className="flex items-center gap-2 text-[10px] font-mono">
                    <span className="text-gray-600 w-8">#{i}</span>
                    <div className="flex-1 h-1 bg-gray-800 rounded-full overflow-hidden">
                      <div
                        className={`h-full rounded-full ${scoreBg(step.score)}`}
                        style={{ width: `${step.score * 100}%` }}
                      />
                    </div>
                    <span className={scoreColor(step.score)}>{step.score.toFixed(2)}</span>
                  </div>
                ))}
                {score.reasoning && (
                  <p className="text-[10px] text-gray-500 mt-2 italic">{score.reasoning}</p>
                )}
              </div>
            )}
          </div>
        ))}
      </div>
    </div>
  )
}
