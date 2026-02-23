import { useState } from 'react'

interface Props {
  onSubmit: (intent: string, constraints: string[], context: Record<string, unknown>) => void
  isRunning: boolean
}

export default function IntentPanel({ onSubmit, isRunning }: Props) {
  const [intent, setIntent] = useState('')
  const [constraints, setConstraints] = useState<string[]>([''])
  const [contextJson, setContextJson] = useState('{}')
  const [contextError, setContextError] = useState('')

  const addConstraint = () => setConstraints([...constraints, ''])
  const removeConstraint = (i: number) => setConstraints(constraints.filter((_, idx) => idx !== i))
  const updateConstraint = (i: number, val: string) => {
    const next = [...constraints]
    next[i] = val
    setConstraints(next)
  }

  const handleSubmit = () => {
    try {
      const ctx = JSON.parse(contextJson)
      setContextError('')
      onSubmit(
        intent,
        constraints.filter((c) => c.trim() !== ''),
        ctx,
      )
    } catch {
      setContextError('Invalid JSON')
    }
  }

  return (
    <div className="space-y-4">
      <h2 className="text-lg font-semibold text-gray-200">Intent</h2>

      <textarea
        value={intent}
        onChange={(e) => setIntent(e.target.value)}
        placeholder="Describe what you want LATTICE to do..."
        className="w-full h-28 bg-gray-800 border border-gray-700 rounded-lg p-3 text-gray-100 placeholder-gray-500 focus:border-indigo-500 focus:ring-1 focus:ring-indigo-500 outline-none resize-none"
      />

      <div>
        <div className="flex items-center justify-between mb-2">
          <label className="text-sm font-medium text-gray-400">Constraints</label>
          <button
            onClick={addConstraint}
            className="text-xs text-indigo-400 hover:text-indigo-300"
          >
            + Add
          </button>
        </div>
        <div className="space-y-2">
          {constraints.map((c, i) => (
            <div key={i} className="flex gap-2">
              <input
                value={c}
                onChange={(e) => updateConstraint(i, e.target.value)}
                placeholder="e.g. Do not suggest layoffs"
                className="flex-1 bg-gray-800 border border-gray-700 rounded px-3 py-1.5 text-sm text-gray-100 placeholder-gray-500 focus:border-indigo-500 outline-none"
              />
              {constraints.length > 1 && (
                <button
                  onClick={() => removeConstraint(i)}
                  className="text-gray-500 hover:text-red-400 text-sm px-2"
                >
                  x
                </button>
              )}
            </div>
          ))}
        </div>
      </div>

      <div>
        <label className="text-sm font-medium text-gray-400 block mb-2">Context (JSON)</label>
        <textarea
          value={contextJson}
          onChange={(e) => setContextJson(e.target.value)}
          className="w-full h-20 bg-gray-800 border border-gray-700 rounded-lg p-3 text-sm font-mono text-gray-100 focus:border-indigo-500 outline-none resize-none"
        />
        {contextError && <p className="text-red-400 text-xs mt-1">{contextError}</p>}
      </div>

      <button
        onClick={handleSubmit}
        disabled={!intent.trim() || isRunning}
        className="w-full py-2.5 bg-indigo-600 hover:bg-indigo-500 disabled:bg-gray-700 disabled:text-gray-500 rounded-lg font-medium transition-colors"
      >
        {isRunning ? 'Running...' : 'Run Pipeline'}
      </button>
    </div>
  )
}
