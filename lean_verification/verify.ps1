param([switch]$CoreOnly)
$ErrorActionPreference = 'Stop'
Set-Location -LiteralPath $PSScriptRoot
$elanBin = Join-Path $env:USERPROFILE '.elan/bin'
if (Test-Path -LiteralPath $elanBin) { $env:PATH = $elanBin + ';' + $env:PATH }
$lakeCommand = Get-Command lake -CommandType Application -ErrorAction SilentlyContinue
if (-not $lakeCommand) {
    Write-Output 'NOT VERIFIED: lake/Lean is not available on PATH. No certificate issued.'
    exit 2
}
& lake env lean --version
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
$modules = @('VietorisOmegaOne/Model', 'VietorisOmegaOne/Diagonal')
if (-not $CoreOnly) {
    $modules += @('VietorisOmegaOne/TopologyProof', 'VietorisOmegaOne/Countability', 'VietorisOmegaOne/OrderModel', 'VietorisOmegaOne/OrderResult', 'VietorisOmegaOne/Results', 'VietorisOmegaOne')
}
foreach ($module in $modules) {
    $outputFile = Join-Path '.lake/build/lib/lean' ($module + '.olean')
    New-Item -ItemType Directory -Force -Path (Split-Path $outputFile) | Out-Null
    Write-Output ('Checking ' + $module + '.lean')
    & lake env lean ($module + '.lean') -o $outputFile
    if ($LASTEXITCODE -ne 0) {
        Write-Output 'NOT VERIFIED: compilation failed. No certificate issued.'
        exit $LASTEXITCODE
    }
}
if ($CoreOnly) {
    & lake env lean CoreAudit.lean
    $auditExit = $LASTEXITCODE
    Write-Output 'CORE-ONLY CHECK: this is not certification of the paper.'
    exit $auditExit
}
$auditOutput = @(& lake env lean FullAudit.lean 2>&1)
$auditExit = $LASTEXITCODE
$auditOutput | ForEach-Object { Write-Output $_ }
if ($auditExit -ne 0) {
    Write-Output 'NOT VERIFIED: the full theorem audit failed. No certificate issued.'
    exit $auditExit
}
$auditText = $auditOutput -join "`n"
$axiomReport = [regex]::Match($auditText, "VietorisOmegaOne.order_model_theorem'? depends on axioms:\s*\[([^\]]*)\]")
if (-not $axiomReport.Success) {
    Write-Output 'NOT VERIFIED: the final theorem axiom report is missing.'
    exit 3
}
$allowedAxioms = @('propext', 'Classical.choice', 'Quot.sound')
$reportedAxioms = $axiomReport.Groups[1].Value.Split(',') | ForEach-Object { $_.Trim() } | Where-Object { $_ }
foreach ($axiomName in $reportedAxioms) {
    if ($axiomName -notin $allowedAxioms) {
        Write-Output ('NOT VERIFIED: unexpected axiom ' + $axiomName)
        exit 4
    }
}
Write-Output 'VERIFIED: the exact final theorem compiled and its axiom report passed. See README.md for source correspondence and scope.'
exit 0
