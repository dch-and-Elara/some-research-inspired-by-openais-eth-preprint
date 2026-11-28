param(
    [Parameter(Mandatory = $true)][string]$LogDirectory
)

$ErrorActionPreference = 'Stop'
$outputDirectory = [IO.Directory]::CreateDirectory($LogDirectory).FullName
$runDirectory = Join-Path $outputDirectory (Get-Date -Format 'yyyyMMdd-HHmmss-ffff')
[IO.Directory]::CreateDirectory($runDirectory) | Out-Null
Push-Location $PSScriptRoot
try {
    function Invoke-RecordedLake([string]$Name, [string[]]$Arguments) {
        & lake @Arguments 2>&1 | Tee-Object -FilePath (Join-Path $runDirectory $Name)
        if ($LASTEXITCODE -ne 0) { throw "lake $($Arguments -join ' ') failed with exit code $LASTEXITCODE" }
    }
    Invoke-RecordedLake 'toolchain.log' @('env', 'lean', '--version')
    Invoke-RecordedLake 'build.log' @('build')
    Invoke-RecordedLake 'axioms.log' @('env', 'lean', 'Audit.lean')
    $axioms = Get-Content -LiteralPath (Join-Path $runDirectory 'axioms.log') -Raw
    $printed = @(Select-String -LiteralPath Audit.lean -Pattern '^#print axioms ')
    $outputs = [regex]::Matches($axioms, "'([^']+)' depends on axioms:\s*\[([^\]]*)\]")
    if ($outputs.Count -ne $printed.Count) { throw 'Unexpected number or format of axiom reports' }
    foreach ($row in $outputs) {
        foreach ($dependency in ($row.Groups[2].Value -split ',\s*')) {
            if ($dependency.Trim() -notin @('propext', 'Classical.choice', 'Quot.sound')) {
                throw "Unexpected axiom $dependency in $($row.Groups[1].Value)"
            }
        }
    }
    $sources = @(Get-ChildItem -LiteralPath BooleanCube -Filter '*.lean' -File -Recurse)
    $sources += @(Get-Item -LiteralPath BooleanCube.lean,Audit.lean)
    $holes = @($sources | Select-String -Pattern '\b(sorry|admit|axiom)\b')
    if ($holes.Count) { throw "Proof placeholder or axiom declaration found in $($holes[0].Path)" }
    $sources | Get-FileHash -Algorithm SHA256 | ForEach-Object {
        '{0}  {1}' -f $_.Hash.ToLowerInvariant(), [IO.Path]::GetRelativePath($PSScriptRoot,$_.Path)
    } | Set-Content -LiteralPath (Join-Path $runDirectory 'source-sha256.txt')
    "Verified $($outputs.Count) axiom reports. Logs: $runDirectory"
}
finally { Pop-Location }
