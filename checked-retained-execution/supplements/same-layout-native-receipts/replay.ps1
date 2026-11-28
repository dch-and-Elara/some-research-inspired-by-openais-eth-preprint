[CmdletBinding()]
param([string]$Lean='lean',[Parameter(Mandatory=$true)][string[]]$BaseLeanPath)
$ErrorActionPreference='Stop'
$root=$PSScriptRoot
$modules=Get-Content (Join-Path $root 'MODULES.json') -Raw | ConvertFrom-Json
$build=Join-Path $root ('replay-'+[DateTime]::UtcNow.ToString('yyyyMMdd-HHmmssfff'))
[void](New-Item -ItemType Directory $build)
$env:LEAN_PATH=(@($build)+$BaseLeanPath) -join [IO.Path]::PathSeparator
foreach($m in $modules){Copy-Item -LiteralPath (Join-Path $root "lean/$m.lean") -Destination $build}
Push-Location $build
try {
 foreach($m in $modules){
  $lines=& $Lean -j 1 -DwarningAsError=true -o "$m.olean" "$m.lean" 2>&1
  $code=$LASTEXITCODE
  $lines|Out-File -Encoding utf8 "$m.log"
  $t=$lines -join [Environment]::NewLine
  if($code -ne 0 -or $t -match 'sorryAx|error:|warning:'){throw "Failed: $m; see $build"}
  foreach($a in [regex]::Matches($t,'depends on axioms:\s*\[([^\]]*)\]')){
   foreach($x in $a.Groups[1].Value.Split(',')){if($x.Trim() -notin @('propext','Classical.choice','Quot.sound')){throw "Unexpected axiom $x in $m"}}
  }
 }
 Write-Output "Strict replay passed: $($modules.Count) modules."
} finally {Pop-Location}