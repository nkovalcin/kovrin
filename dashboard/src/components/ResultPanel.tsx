interface Props {
  output: string
  success: boolean
}

export default function ResultPanel({ output, success }: Props) {
  if (!output) {
    return <p className="text-gray-500 text-sm">No results yet. Run a pipeline to see output.</p>
  }

  return (
    <div className="space-y-3">
      <div className="flex items-center gap-3">
        <h2 className="text-lg font-semibold text-gray-200">Result</h2>
        <span className={`text-xs px-2 py-0.5 rounded font-medium ${
          success ? 'bg-green-500/20 text-green-400' : 'bg-red-500/20 text-red-400'
        }`}>
          {success ? 'SUCCESS' : 'FAILED'}
        </span>
      </div>
      <div className="bg-gray-800 border border-gray-700 rounded-lg p-4 text-sm text-gray-200 whitespace-pre-wrap font-mono leading-relaxed max-h-[60vh] overflow-y-auto">
        {output}
      </div>
    </div>
  )
}
