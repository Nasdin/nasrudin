# One-line installer for the Nasrudin discovery worker (Windows).
#
#   $env:NASRUDIN_WORKER_KEY="nsk_worker_..."; iwr -useb https://nasrudin.org/install.ps1 | iex
#
# What it does:
#   1. checks NASRUDIN_WORKER_KEY is set
#   2. installs `elan` (the Lean toolchain manager) if `lake.exe` isn't on PATH
#   3. downloads nasrudin-worker-windows-x86_64.zip from the latest release
#   4. extracts to %USERPROFILE%\.nasrudin\worker (override with $env:NASRUDIN_WORKER_DIR)
#   5. starts run.ps1, which warms the Mathlib cache on first run and submits
#      verified theorems to api.nasrudin.org
#
# Required env: NASRUDIN_WORKER_KEY  (nsk_worker_… from /api-keys)
# Optional env: NASRUDIN_API_URL     (default https://api.nasrudin.org)
#               NASRUDIN_WORKER_DIR  (default $env:USERPROFILE\.nasrudin\worker)
#               NASRUDIN_WORKER_ID   (default $env:COMPUTERNAME)

$ErrorActionPreference = "Stop"

$Repo = "Nasdin/nasrudin"
$Sku  = "windows-x86_64"
$Ext  = "zip"
$InstallDir = if ($env:NASRUDIN_WORKER_DIR) { $env:NASRUDIN_WORKER_DIR } else { Join-Path $env:USERPROFILE ".nasrudin\worker" }

# ── 0. require key ─────────────────────────────────────────────────────────
if (-not $env:NASRUDIN_WORKER_KEY) {
    Write-Host "[install] error: NASRUDIN_WORKER_KEY is required." -ForegroundColor Red
    Write-Host ""
    Write-Host "  Get a worker key:"
    Write-Host "    1. Sign in at https://nasrudin.org/signin"
    Write-Host "    2. Open /api-keys -> '+ New key' -> Kind: Worker"
    Write-Host "    3. Copy the nsk_worker_... value"
    Write-Host ""
    Write-Host "  Then run, replacing nsk_worker_... with the value you copied:"
    Write-Host '    $env:NASRUDIN_WORKER_KEY="nsk_worker_..."; iwr -useb https://nasrudin.org/install.ps1 | iex'
    exit 1
}

Write-Host "[install] platform: $Sku"

# ── 2. ensure elan + lake ──────────────────────────────────────────────────
if (-not (Get-Command lake.exe -ErrorAction SilentlyContinue)) {
    Write-Host "[install] Lean toolchain (lake) not on PATH — installing elan…"
    $ElanInit = Join-Path $env:TEMP "elan-init.ps1"
    Invoke-WebRequest -UseBasicParsing -Uri "https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1" -OutFile $ElanInit
    & $ElanInit -y --default-toolchain none
    Remove-Item -Path $ElanInit -Force -ErrorAction SilentlyContinue
    $ElanBin = Join-Path $env:USERPROFILE ".elan\bin"
    $env:Path = "$ElanBin;$env:Path"
    if (-not (Get-Command lake.exe -ErrorAction SilentlyContinue)) {
        Write-Host "[install] error: elan installed but lake.exe still not on PATH" -ForegroundColor Red
        Write-Host "[install]   restart your shell, then re-run this command"
        exit 1
    }
}

# ── 3. download bundle ────────────────────────────────────────────────────
$Url = "https://github.com/$Repo/releases/latest/download/nasrudin-worker-$Sku.$Ext"
$TmpZip = Join-Path $env:TEMP ("nasrudin-worker-" + [guid]::NewGuid().ToString("N") + ".zip")
Write-Host "[install] downloading $Url"
try {
    Invoke-WebRequest -UseBasicParsing -Uri $Url -OutFile $TmpZip
} catch {
    Write-Host "[install] error: download failed (network? release missing?)" -ForegroundColor Red
    exit 1
}

# Optional sha256 verification.
$ShaUrl = "$Url.sha256"
try {
    $ShaText = (Invoke-WebRequest -UseBasicParsing -Uri $ShaUrl).Content
    $Expected = ($ShaText -split '\s+')[0].ToLower()
    $Actual   = (Get-FileHash -Path $TmpZip -Algorithm SHA256).Hash.ToLower()
    if ($Expected -ne $Actual) {
        Write-Host "[install] error: sha256 mismatch — expected $Expected got $Actual" -ForegroundColor Red
        exit 1
    }
    Write-Host "[install] sha256 verified"
} catch {
    # sidecar missing or unreachable — proceed without verification
}

# ── 4. extract ─────────────────────────────────────────────────────────────
if (Test-Path $InstallDir) { Remove-Item -Path $InstallDir -Recurse -Force }
New-Item -ItemType Directory -Path $InstallDir -Force | Out-Null
Write-Host "[install] extracting to $InstallDir"
Expand-Archive -Path $TmpZip -DestinationPath $InstallDir -Force
# Bundle archives one wrapping nasrudin-worker-windows-x86_64\ dir; flatten it.
$Inner = Join-Path $InstallDir "nasrudin-worker-$Sku"
if (Test-Path $Inner) {
    Get-ChildItem -Path $Inner -Force | Move-Item -Destination $InstallDir -Force
    Remove-Item -Path $Inner -Recurse -Force
}
Remove-Item -Path $TmpZip -Force

# ── 5. run ─────────────────────────────────────────────────────────────────
Set-Location $InstallDir
$ApiUrl   = if ($env:NASRUDIN_API_URL) { $env:NASRUDIN_API_URL } else { "https://api.nasrudin.org" }
$WorkerId = if ($env:NASRUDIN_WORKER_ID) { $env:NASRUDIN_WORKER_ID } else { $env:COMPUTERNAME }
Write-Host ""
Write-Host "[install] starting worker (Ctrl+C to stop)"
Write-Host "[install]   bundle:    $InstallDir"
Write-Host "[install]   api:       $ApiUrl"
Write-Host "[install]   worker_id: $WorkerId"
Write-Host ""
& "$InstallDir\run.ps1"
