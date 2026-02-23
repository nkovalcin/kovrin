import type { ViewMode } from '../types/kovrin'

const VIEW_MODES: { mode: ViewMode; label: string; desc: string }[] = [
  { mode: 'OPERATOR', label: 'Operator', desc: 'High-level overview' },
  { mode: 'ANALYST', label: 'Analyst', desc: 'Task-level detail' },
  { mode: 'DEVELOPER', label: 'Developer', desc: 'Full trace data' },
]

interface Props {
  viewMode: ViewMode
  onChange: (mode: ViewMode) => void
}

export default function ViewModeSelector({ viewMode, onChange }: Props) {
  return (
    <div className="flex gap-1 bg-gray-800 rounded-lg p-1">
      {VIEW_MODES.map(({ mode, label, desc }) => (
        <button
          key={mode}
          onClick={() => onChange(mode)}
          className={`px-3 py-1.5 rounded-md text-xs font-medium transition-colors ${
            viewMode === mode
              ? 'bg-blue-600 text-white'
              : 'text-gray-400 hover:text-gray-200 hover:bg-gray-700'
          }`}
          title={desc}
        >
          {label}
        </button>
      ))}
    </div>
  )
}
