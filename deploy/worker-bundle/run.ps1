# Nasrudin discovery worker — public bundle launcher (Windows / PowerShell).
#
# Required env: NASRUDIN_WORKER_KEY (nsk_worker_...)
# Optional env: NASRUDIN_API_URL    (default https://api.nasrudin.org)
#               NASRUDIN_WORKER_ID  (default $env:COMPUTERNAME)

$ErrorActionPreference = "Stop"

Set-Location -Path $PSScriptRoot

if (-not $env:NASRUDIN_WORKER_KEY) {
    Write-Error "NASRUDIN_WORKER_KEY is required. Get one at https://nasrudin.org/api-keys (Kind: Worker)."
    exit 1
}

if (-not $env:NASRUDIN_API_URL)   { $env:NASRUDIN_API_URL   = "https://api.nasrudin.org" }
if (-not $env:NASRUDIN_WORKER_ID) { $env:NASRUDIN_WORKER_ID = $env:COMPUTERNAME }

if (-not (Get-Command lake.exe -ErrorAction SilentlyContinue)) {
    Write-Host "error: 'lake' (Lean toolchain) not found on PATH." -ForegroundColor Red
    Write-Host "  Install elan via PowerShell:"
    Write-Host "    iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex"
    Write-Host "  Then restart your shell."
    exit 1
}

if (-not (Test-Path "prover\.lake")) {
    Write-Host "[worker] first run: warming Mathlib cache (this takes a few minutes)..."
    Push-Location prover
    try { lake exe cache get | Out-Null } catch { }
    Pop-Location
}

Write-Host "[worker] api=$($env:NASRUDIN_API_URL)  id=$($env:NASRUDIN_WORKER_ID)"
& ".\nasrudin-worker.exe" --verify ".\prover" @args
exit $LASTEXITCODE
