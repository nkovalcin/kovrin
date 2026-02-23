import { useState } from 'react'
import type { AutonomyProfile, AutonomySettings, RoutingAction } from '../types/kovrin'
import { updateAutonomy } from '../api/client'

const PROFILES: { id: AutonomyProfile; label: string; desc: string }[] = [
  { id: 'DEFAULT', label: 'Default', desc: 'Standard routing matrix' },
  { id: 'CAUTIOUS', label: 'Cautious', desc: 'More human approvals' },
  { id: 'AGGRESSIVE', label: 'Aggressive', desc: 'More auto-execution' },
  { id: 'LOCKED', label: 'Locked', desc: 'All tasks need approval' },
]

const RISK_LEVELS = ['LOW', 'MEDIUM', 'HIGH', 'CRITICAL'] as const
const SPEC_TIERS = ['FREE', 'GUARDED', 'NONE'] as const
const ACTIONS: RoutingAction[] = ['AUTO_EXECUTE', 'SANDBOX_REVIEW', 'HUMAN_APPROVAL']

const ACTION_COLORS: Record<RoutingAction, string> = {
  AUTO_EXECUTE: 'bg-green-500/20 text-green-400 border-green-500/30',
  SANDBOX_REVIEW: 'bg-yellow-500/20 text-yellow-400 border-yellow-500/30',
  HUMAN_APPROVAL: 'bg-red-500/20 text-red-400 border-red-500/30',
}

const ACTION_LABELS: Record<RoutingAction, string> = {
  AUTO_EXECUTE: 'AUTO',
  SANDBOX_REVIEW: 'SANDBOX',
  HUMAN_APPROVAL: 'HUMAN',
}

// Default routing matrix
const DEFAULT_MATRIX: Record<string, RoutingAction> = {
  'LOW:FREE': 'AUTO_EXECUTE',
  'LOW:GUARDED': 'AUTO_EXECUTE',
  'LOW:NONE': 'SANDBOX_REVIEW',
  'MEDIUM:FREE': 'AUTO_EXECUTE',
  'MEDIUM:GUARDED': 'SANDBOX_REVIEW',
  'MEDIUM:NONE': 'HUMAN_APPROVAL',
  'HIGH:FREE': 'SANDBOX_REVIEW',
  'HIGH:GUARDED': 'HUMAN_APPROVAL',
  'HIGH:NONE': 'HUMAN_APPROVAL',
  'CRITICAL:FREE': 'HUMAN_APPROVAL',
  'CRITICAL:GUARDED': 'HUMAN_APPROVAL',
  'CRITICAL:NONE': 'HUMAN_APPROVAL',
}

interface Props {
  settings: AutonomySettings
  onUpdated: (settings: AutonomySettings) => void
}

export default function AutonomyControls({ settings, onUpdated }: Props) {
  const [profile, setProfile] = useState<AutonomyProfile>(settings.profile)
  const [overrides, setOverrides] = useState<Record<string, string>>(settings.override_matrix)
  const [saving, setSaving] = useState(false)

  const handleCellClick = (key: string) => {
    // CRITICAL row is locked
    if (key.startsWith('CRITICAL:')) return

    const current = overrides[key] || DEFAULT_MATRIX[key] || 'HUMAN_APPROVAL'
    const idx = ACTIONS.indexOf(current as RoutingAction)
    const next = ACTIONS[(idx + 1) % ACTIONS.length]
    setOverrides({ ...overrides, [key]: next })
  }

  const handleApply = async () => {
    setSaving(true)
    try {
      const result = await updateAutonomy(profile, overrides)
      onUpdated(result)
    } finally {
      setSaving(false)
    }
  }

  const handleReset = () => {
    setProfile(settings.profile)
    setOverrides(settings.override_matrix)
  }

  const getEffectiveAction = (key: string): RoutingAction => {
    if (overrides[key]) return overrides[key] as RoutingAction
    return DEFAULT_MATRIX[key] || 'HUMAN_APPROVAL'
  }

  return (
    <div className="space-y-4">
      <h2 className="text-lg font-semibold text-gray-200">Autonomy Controls</h2>

      {/* Profile selector */}
      <div className="grid grid-cols-4 gap-2">
        {PROFILES.map(({ id, label, desc }) => (
          <button
            key={id}
            onClick={() => setProfile(id)}
            className={`border rounded-lg px-3 py-2 text-left transition-colors ${
              profile === id
                ? 'border-blue-500 bg-blue-500/10 text-blue-300'
                : 'border-gray-700 bg-gray-800 text-gray-400 hover:border-gray-600'
            }`}
          >
            <div className="text-sm font-medium">{label}</div>
            <div className="text-[10px] text-gray-500">{desc}</div>
          </button>
        ))}
      </div>

      {/* 4x3 routing matrix grid */}
      <div>
        <div className="text-xs text-gray-500 mb-2 font-mono">Override Matrix (click cells to cycle)</div>
        <div className="grid grid-cols-4 gap-1 text-center">
          {/* Header */}
          <div className="text-[10px] text-gray-600 font-mono" />
          {SPEC_TIERS.map((tier) => (
            <div key={tier} className="text-[10px] text-gray-500 font-mono py-1">{tier}</div>
          ))}

          {/* Rows */}
          {RISK_LEVELS.map((risk) => (
            <>
              <div key={`label-${risk}`} className="text-[10px] text-gray-500 font-mono py-2 text-right pr-2">{risk}</div>
              {SPEC_TIERS.map((tier) => {
                const key = `${risk}:${tier}`
                const action = getEffectiveAction(key)
                const isOverridden = key in overrides
                const isCritical = risk === 'CRITICAL'
                return (
                  <button
                    key={key}
                    onClick={() => handleCellClick(key)}
                    disabled={isCritical}
                    className={`border rounded px-1 py-2 text-[10px] font-mono transition-colors ${
                      ACTION_COLORS[action]
                    } ${isCritical ? 'opacity-50 cursor-not-allowed' : 'cursor-pointer hover:opacity-80'} ${
                      isOverridden ? 'ring-1 ring-blue-500/50' : ''
                    }`}
                    title={isCritical ? 'CRITICAL always requires human approval' : `Click to change: ${key}`}
                  >
                    {ACTION_LABELS[action]}
                  </button>
                )
              })}
            </>
          ))}
        </div>
      </div>

      {/* Apply / Reset */}
      <div className="flex gap-2">
        <button
          onClick={handleApply}
          disabled={saving}
          className="bg-blue-600 hover:bg-blue-700 text-white px-4 py-1.5 rounded text-sm disabled:opacity-50"
        >
          {saving ? 'Saving...' : 'Apply'}
        </button>
        <button
          onClick={handleReset}
          className="bg-gray-700 hover:bg-gray-600 text-gray-300 px-4 py-1.5 rounded text-sm"
        >
          Reset
        </button>
      </div>

      {/* Current settings info */}
      <div className="text-[10px] text-gray-600 font-mono">
        Last updated: {new Date(settings.updated_at).toLocaleString()}
      </div>
    </div>
  )
}
