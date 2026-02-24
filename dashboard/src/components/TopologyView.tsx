import { useState, useEffect } from 'react'
import type { TopologyType } from '../types/kovrin'
import { getTopology } from '../api/client'

const TOPO_COLORS: Record<TopologyType, string> = {
  SEQUENTIAL: 'bg-blue-500/20 text-blue-400',
  PARALLEL: 'bg-green-500/20 text-green-400',
  PIPELINE: 'bg-purple-500/20 text-purple-400',
  MAP_REDUCE: 'bg-amber-500/20 text-amber-400',
  HIERARCHICAL: 'bg-cyan-500/20 text-cyan-400',
}

const TOPO_ICONS: Record<TopologyType, string> = {
  SEQUENTIAL: '\u2192 \u2192 \u2192',
  PARALLEL: '\u2016 \u2016 \u2016',
  PIPELINE: '\u21D2 \u21D2 \u21D2',
  MAP_REDUCE: '< \u2016 >',
  HIERARCHICAL: '\u2193 / \\',
}

interface Props {
  intentId: string | null
}

export default function TopologyView({ intentId }: Props) {
  const [topology, setTopology] = useState<TopologyType | null>(null)
  const [confidence, setConfidence] = useState(0)
  const [reasoning, setReasoning] = useState('')
  const [metrics, setMetrics] = useState<Record<string, unknown>>({})
  const [loading, setLoading] = useState(false)

  useEffect(() => {
    if (!intentId) return
    setLoading(true)
    getTopology(intentId)
      .then((r) => {
        setTopology(r.topology as TopologyType || null)
        setConfidence(r.confidence || 0)
        setReasoning(r.reasoning || '')
        setMetrics(r.graph_metrics || {})
      })
      .finally(() => setLoading(false))
  }, [intentId])

  if (!intentId) {
    return null
  }

  if (loading) {
    return <div className="text-[10px] text-gray-500">Analyzing topology...</div>
  }

  if (!topology) {
    return null
  }

  const colorClass = TOPO_COLORS[topology] || 'bg-gray-700 text-gray-400'
  const icon = TOPO_ICONS[topology] || ''

  return (
    <div className="border border-gray-700 rounded-lg p-3 space-y-2">
      <div className="flex items-center gap-2">
        <span className="text-xs text-gray-400 font-medium">Topology</span>
        <span className={`text-xs font-mono font-bold px-2 py-0.5 rounded ${colorClass}`}>
          {icon} {topology}
        </span>
        <span className="text-[10px] text-gray-500 font-mono ml-auto">
          confidence: {(confidence * 100).toFixed(0)}%
        </span>
      </div>

      {reasoning && (
        <p className="text-[10px] text-gray-500">{reasoning}</p>
      )}

      {Object.keys(metrics).length > 0 && (
        <div className="flex gap-3 flex-wrap">
          {Object.entries(metrics).map(([key, val]) => {
            if (typeof val !== 'number' && typeof val !== 'string') return null
            return (
              <div key={key} className="text-[10px] font-mono">
                <span className="text-gray-600">{key}: </span>
                <span className="text-gray-400">{String(val)}</span>
              </div>
            )
          })}
        </div>
      )}
    </div>
  )
}
