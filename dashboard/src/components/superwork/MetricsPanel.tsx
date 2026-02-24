import { useEffect, useState } from 'react'
import type { MetricsSnapshot, PredictionResult } from '../../types/kovrin'
import { getSuperWorkMetrics, getSuperWorkPrediction } from '../../api/client'

interface Props {
  metrics: MetricsSnapshot | null
  onMetricsChange: (m: MetricsSnapshot) => void
}

export default function MetricsPanel({ metrics, onMetricsChange }: Props) {
  const [prediction, setPrediction] = useState<PredictionResult | null>(null)
  const [remainingInput, setRemainingInput] = useState('10')
  const [loading, setLoading] = useState(false)

  useEffect(() => {
    const interval = setInterval(async () => {
      try {
        const m = await getSuperWorkMetrics()
        if (!('error' in m)) {
          onMetricsChange(m)
        }
      } catch {
        // silent
      }
    }, 5000)
    return () => clearInterval(interval)
  }, [onMetricsChange])

  const handlePredict = async () => {
    const remaining = parseInt(remainingInput, 10)
    if (isNaN(remaining) || remaining < 1) return
    setLoading(true)
    try {
      const p = await getSuperWorkPrediction(remaining)
      if (!('error' in p)) {
        setPrediction(p)
      }
    } catch {
      // error
    } finally {
      setLoading(false)
    }
  }

  if (!metrics) {
    return (
      <div className="bg-gray-800/50 border border-gray-700 p-4">
        <p className="text-xs text-gray-500">No metrics yet. Start a session first.</p>
      </div>
    )
  }

  return (
    <div className="space-y-3">
      {/* Metrics Grid */}
      <div className="grid grid-cols-2 gap-2">
        <MetricCard label="Tasks Done" value={metrics.tasks_completed} color="text-green-400" />
        <MetricCard label="Tasks Failed" value={metrics.tasks_failed} color="text-red-400" />
        <MetricCard
          label="Velocity"
          value={`${metrics.velocity_tasks_per_hour.toFixed(1)}/hr`}
          color="text-blue-400"
        />
        <MetricCard
          label="Cost"
          value={`$${metrics.cost_usd.toFixed(2)}`}
          color="text-amber-400"
        />
      </div>

      {/* Success Rate Bar */}
      {metrics.success_rate !== undefined && (
        <div className="bg-gray-800/50 border border-gray-700 p-3">
          <div className="flex justify-between text-xs mb-1">
            <span className="text-gray-500">Success Rate</span>
            <span className="text-gray-400 font-mono">{(metrics.success_rate * 100).toFixed(0)}%</span>
          </div>
          <div className="h-1.5 bg-gray-700">
            <div
              className={`h-full transition-all ${
                metrics.success_rate > 0.8 ? 'bg-green-400' :
                metrics.success_rate > 0.5 ? 'bg-amber-400' : 'bg-red-400'
              }`}
              style={{ width: `${metrics.success_rate * 100}%` }}
            />
          </div>
        </div>
      )}

      {/* Prediction */}
      <div className="bg-gray-800/50 border border-gray-700 p-3">
        <h4 className="text-xs font-semibold text-gray-400 mb-2">Predict Completion</h4>
        <div className="flex gap-2 mb-2">
          <input
            type="number"
            min="1"
            value={remainingInput}
            onChange={(e) => setRemainingInput(e.target.value)}
            className="w-20 bg-gray-900 border border-gray-700 px-2 py-1 text-xs font-mono text-gray-300 focus:outline-none focus:border-emerald-500"
          />
          <span className="text-xs text-gray-500 self-center">tasks remaining</span>
          <button
            onClick={handlePredict}
            disabled={loading}
            className="ml-auto text-[10px] font-mono bg-emerald-500/20 text-emerald-300 hover:bg-emerald-500/30 px-2 py-1 border border-emerald-500/30 transition-colors disabled:opacity-40"
          >
            {loading ? '...' : 'PREDICT'}
          </button>
        </div>

        {prediction && (
          <div className="space-y-1 text-xs">
            <div className="flex justify-between">
              <span className="text-gray-500">Est. Time</span>
              <span className="text-gray-300 font-mono">{prediction.estimated_hours.toFixed(1)}h</span>
            </div>
            <div className="flex justify-between">
              <span className="text-gray-500">Est. Cost</span>
              <span className="text-gray-300 font-mono">${prediction.estimated_cost_usd.toFixed(2)}</span>
            </div>
            <div className="flex justify-between">
              <span className="text-gray-500">Confidence</span>
              <span className={`font-mono ${
                prediction.confidence > 0.7 ? 'text-green-400' :
                prediction.confidence > 0.4 ? 'text-amber-400' : 'text-red-400'
              }`}>
                {(prediction.confidence * 100).toFixed(0)}%
              </span>
            </div>
            {prediction.estimated_completion && (
              <div className="flex justify-between">
                <span className="text-gray-500">ETA</span>
                <span className="text-gray-300 font-mono">
                  {new Date(prediction.estimated_completion).toLocaleTimeString()}
                </span>
              </div>
            )}
          </div>
        )}
      </div>
    </div>
  )
}

function MetricCard({ label, value, color }: { label: string; value: string | number; color: string }) {
  return (
    <div className="bg-gray-800/50 border border-gray-700 p-3">
      <p className="text-[10px] text-gray-500 uppercase tracking-wider">{label}</p>
      <p className={`text-lg font-mono font-bold ${color}`}>{value}</p>
    </div>
  )
}
