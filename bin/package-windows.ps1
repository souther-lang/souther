#!/usr/bin/env pwsh
# Writes the two Windows distributions of the command line into souther-cli/target/dist:
#
#   souther-<version>-windows-x64.zip        souther.exe beside a Java runtime of its own
#   souther-<version>-windows-x64-nojre.zip  souther.cmd over a Java the machine already has
#
# Run it on Windows, after `mvn package` has written the shaded jar and the launcher: jpackage
# builds an image for the platform it runs on, and the console launcher it writes is a Windows one.
#
#   mvn -B -DskipTests package
#   bin/package-windows.ps1

[CmdletBinding()]
param()

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
Add-Type -AssemblyName System.IO.Compression.FileSystem

$root = Split-Path -Parent (Split-Path -Parent $PSCommandPath)
$target = Join-Path $root 'souther-cli/target'
$jar = Join-Path $target 'souther.jar'
$launcher = Join-Path $target 'launcher/souther.cmd'
foreach ($file in @($jar, $launcher)) {
    if (-not (Test-Path $file)) { throw "$file is missing: package the reactor first" }
}

# The build stamps the version into the jar, and asking the jar is asking the thing being packaged:
# a version read from anywhere else is a second answer that can differ from this one.
$Version = $null
$open = [IO.Compression.ZipFile]::OpenRead($jar)
try {
    $stamp = $open.GetEntry('META-INF/maven/org.souther-lang/souther-cli/pom.properties')
    if (-not $stamp) { throw "$jar carries no version stamp" }
    $reader = New-Object IO.StreamReader($stamp.Open())
    try {
        while ($null -ne ($line = $reader.ReadLine())) {
            if ($line -match '^version=(.+)$') { $Version = $Matches[1].Trim() }
        }
    }
    finally { $reader.Dispose() }
}
finally { $open.Dispose() }
if (-not $Version) { throw "$jar states no version" }
Write-Host "packaging souther $Version"

# jpackage takes a version of one to three integers. A Maven version carries a qualifier after a
# hyphen on everything that is not a final release, and what the archives are named by keeps it.
$appVersion = ($Version -split '-')[0]

# What the shaded jar reaches, as jdeps reports it. A compiler is among them because `souther japi`
# reads javadoc out of a library's sources; a runtime short of one answers that command with
# nothing, and answers every other command as if it were complete.
$modules = 'java.base,java.compiler,java.desktop,java.sql,java.xml,jdk.compiler'

$dist = Join-Path $target 'dist'
if (Test-Path $dist) { Remove-Item -Recurse -Force $dist }
New-Item -ItemType Directory -Force -Path $dist | Out-Null

$staged = Join-Path $dist 'jar'
New-Item -ItemType Directory -Force -Path $staged | Out-Null
Copy-Item $jar $staged

# --win-console is what makes the launcher a command: without it the image is a windowed
# application, whose standard output and error reach nobody and whose exit code reaches no shell.
# The stack is the one every launcher hands the JVM, and the launchers beside this one say why.
$bundled = Join-Path $dist 'bundled'
jpackage --type app-image `
    --name souther `
    --app-version $appVersion `
    --dest $bundled `
    --input $staged `
    --main-jar souther.jar `
    --main-class souther.cli.Main `
    --add-modules $modules `
    --java-options '-Xss4m' `
    --win-console `
    --vendor 'souther-lang' `
    --description 'The Souther compiler and command line'
if ($LASTEXITCODE -ne 0) { throw "jpackage ended with $LASTEXITCODE" }

# The launcher sits at the root of the image, where jpackage puts the other distribution's, so the
# directory that has to reach a path is `souther` in both and nothing downstream asks which was
# unpacked.
$nojre = Join-Path $dist 'nojre'
New-Item -ItemType Directory -Force -Path (Join-Path $nojre 'souther/lib') | Out-Null
Copy-Item $launcher (Join-Path $nojre 'souther/souther.cmd')
Copy-Item $jar (Join-Path $nojre 'souther/lib/souther.jar')

# Both archives hold a `souther` directory rather than their contents at the root, because WinGet
# names the launcher by a path relative to the root of what it unpacked, and because unpacking one
# by hand into a directory of the user's choosing should not scatter it.
function Write-Zip([string] $from, [string] $to) {
    [System.IO.Compression.ZipFile]::CreateFromDirectory($from, $to)
    Write-Host "wrote $to"
}
Write-Zip $bundled (Join-Path $dist "souther-$Version-windows-x64.zip")
Write-Zip $nojre (Join-Path $dist "souther-$Version-windows-x64-nojre.zip")
