#!/usr/bin/env pwsh
# Installs the Souther command line on Windows from a GitHub Release, for the current user only.
#
#   irm https://raw.githubusercontent.com/souther-lang/souther/main/install.ps1 | iex
#
# Piping to iex passes no arguments, so the form that takes them names the script block:
#
#   & ([scriptblock]::Create((irm https://raw.githubusercontent.com/souther-lang/souther/main/install.ps1))) -Nojdk
#   & ([scriptblock]::Create((irm https://raw.githubusercontent.com/souther-lang/souther/main/install.ps1))) -Uninstall
#
# Everything it writes is under %LOCALAPPDATA%\Programs\souther, which it owns: an uninstall removes
# that directory and the one path entry it added, and touches nothing else. The location is not a
# parameter, because a directory this script is told to remove recursively has to be one it made.

[CmdletBinding()]
param(
    # A release version without the `v`, or the latest release when left out. Required with -From,
    # which has no release to ask.
    [string] $Version,
    # The distribution that expects a JDK 25 on the machine rather than carrying a runtime. A JDK
    # rather than a JRE, because `souther japi` reads javadoc through a compiler.
    [switch] $Nojdk,
    [switch] $Uninstall,
    # A directory holding the archives and a SHA256SUMS over them, instead of a GitHub Release.
    # What packaged them can install them this way without publishing anything.
    [string] $From
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
[Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12
Add-Type -AssemblyName System.IO.Compression.FileSystem

$repository = 'souther-lang/souther'
$InstallDir = Join-Path $env:LOCALAPPDATA 'Programs\souther'
$link = Join-Path $InstallDir 'current'

# The launcher sits at the root of either distribution, so this is the whole of what reaches a path
# and the whole of what an uninstall takes back out.
$entry = $link

# Removed by what it is rather than by what it starts with: a directory of the user's that happens
# to sit beside this one, or under it, is not this script's to take off their path.
function Set-UserPathEntry([bool] $present) {
    $current = [Environment]::GetEnvironmentVariable('Path', 'User')
    $entries = @()
    if ($current) { $entries = @($current -split ';' | Where-Object { $_ }) }
    $kept = @($entries | Where-Object { -not $_.TrimEnd('\').Equals($entry, [StringComparison]::OrdinalIgnoreCase) })
    if ($present) { $kept = $kept + $entry }
    [Environment]::SetEnvironmentVariable('Path', ($kept -join ';'), 'User')
}

# A junction is deleted as the link it is. Removing it the way a directory is removed reaches what
# it points at, which here is a directory under this one.
function Remove-Junction([string] $path) {
    if (Test-Path $path) { [IO.Directory]::Delete($path) }
}

if ($Uninstall) {
    Set-UserPathEntry $false
    Remove-Junction $link
    if (Test-Path $InstallDir) { Remove-Item -Recurse -Force $InstallDir }
    Write-Host 'souther is uninstalled. Open a new terminal for PATH to say so.'
    return
}

if ($From) {
    if (-not $Version) { throw '-From needs -Version: a directory of archives states no latest' }
} elseif (-not $Version) {
    $latest = Invoke-RestMethod "https://api.github.com/repos/$repository/releases/latest"
    $Version = $latest.tag_name -replace '^v', ''
}

$archive = if ($Nojdk) { "souther-$Version-windows-x64-nojdk.zip" } else { "souther-$Version-windows-x64.zip" }

$work = Join-Path ([IO.Path]::GetTempPath()) ("souther-install-" + [Guid]::NewGuid())
New-Item -ItemType Directory -Force -Path $work | Out-Null
try {
    $zip = Join-Path $work $archive
    $sums = Join-Path $work 'SHA256SUMS'
    if ($From) {
        Copy-Item (Join-Path $From $archive) $zip
        Copy-Item (Join-Path $From 'SHA256SUMS') $sums
    } else {
        $base = "https://github.com/$repository/releases/download/v$Version"
        Write-Host "downloading $archive"
        Invoke-WebRequest "$base/$archive" -OutFile $zip
        Invoke-WebRequest "$base/SHA256SUMS" -OutFile $sums
    }

    # One sums file covers every archive, so the line for this one is found by name. An archive the
    # file does not mention is not one the release published.
    $line = Get-Content $sums | Where-Object { $_ -match "\s$([Regex]::Escape($archive))$" }
    if (-not $line) { throw "SHA256SUMS does not mention $archive" }
    $expected = (($line -split '\s+')[0]).ToUpperInvariant()
    $actual = (Get-FileHash $zip -Algorithm SHA256).Hash
    if ($actual -ne $expected) { throw "$archive hashes to $actual and the sums say $expected" }

    # The archive holds a `souther` directory, and the installed version is that directory under a
    # name of its own, so more than one version can sit here and `current` can be pointed at any.
    $unpacked = Join-Path $work 'unpacked'
    [IO.Compression.ZipFile]::ExtractToDirectory($zip, $unpacked)

    $installed = Join-Path $InstallDir $Version
    Remove-Junction $link
    if (Test-Path $installed) { Remove-Item -Recurse -Force $installed }
    New-Item -ItemType Directory -Force -Path $InstallDir | Out-Null
    Move-Item (Join-Path $unpacked 'souther') $installed
    New-Item -ItemType Junction -Path $link -Target $installed | Out-Null
}
finally {
    Remove-Item -Recurse -Force $work -ErrorAction SilentlyContinue
}

Set-UserPathEntry $true

Write-Host "souther $Version is installed in $(Join-Path $InstallDir $Version)."
Write-Host "$entry is on your PATH. Open a new terminal, then run: souther help"
