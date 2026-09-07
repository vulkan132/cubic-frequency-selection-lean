param(
    [string]$Python = 'python',
    [switch]$UseCache
)
$ErrorActionPreference = 'Stop'
$gmzProjectRoot = Split-Path -Parent $PSCommandPath
$gmzOldNoCache = $env:MATHLIB_NO_CACHE_ON_UPDATE
$gmzOldSrc = $env:LEAN_SRC_PATH
$gmzOldCache = $env:MATHLIB_CACHE_DIR
Push-Location -LiteralPath $gmzProjectRoot
try {
    & $Python bootstrap_dependencies.py
    if ($LASTEXITCODE -ne 0) { throw 'Dependency retrieval failed' }
    $env:MATHLIB_NO_CACHE_ON_UPDATE = '1'
    & lake update
    if ($LASTEXITCODE -ne 0) { throw 'Dependency configuration failed' }
    if ($UseCache) {
        & lake build cache
        if ($LASTEXITCODE -ne 0) { throw 'Cache helper build failed' }
        $gmzVendor = Join-Path $gmzProjectRoot 'vendor'
        $gmzMathlib = Join-Path $gmzVendor 'mathlib4-4.33.0'
        $env:LEAN_SRC_PATH = (Get-ChildItem -LiteralPath $gmzVendor -Directory |
            ForEach-Object { $_.FullName }) -join ';'
        $env:MATHLIB_CACHE_DIR = Join-Path $gmzProjectRoot '.lake/mathlib-cache'
        Push-Location -LiteralPath $gmzMathlib
        try {
            & '.lake/build/bin/cache.exe' get Mathlib.Analysis.SpecialFunctions.Complex.Circle `
                Mathlib.Algebra.Order.BigOperators.Ring.Finset Mathlib.Data.Fintype.BigOperators `
                Mathlib.Tactic.Ring Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity `
                Mathlib.Tactic.FieldSimp Mathlib.Analysis.Normed.Group.AddCircle `
                Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds `
                Mathlib.Data.Int.Interval Mathlib.Data.Fintype.EquivFin
            if ($LASTEXITCODE -ne 0) { throw 'Official cache download failed; omit -UseCache to build from source' }
        } finally { Pop-Location }
        $gmzCachePackages = Join-Path $gmzMathlib '.lake/packages'
        if (Test-Path -LiteralPath $gmzCachePackages) {
            Get-ChildItem -LiteralPath $gmzCachePackages -Directory | ForEach-Object {
                Copy-Item -LiteralPath (Join-Path $_.FullName '.lake') `
                    -Destination (Join-Path $gmzVendor $_.Name) -Recurse -Force
            }
        }
    }
    & $Python verify.py
    if ($LASTEXITCODE -ne 0) { throw 'Proof verification failed' }
} finally {
    $env:MATHLIB_NO_CACHE_ON_UPDATE = $gmzOldNoCache
    $env:LEAN_SRC_PATH = $gmzOldSrc
    $env:MATHLIB_CACHE_DIR = $gmzOldCache
    Pop-Location
}
