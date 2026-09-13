#!/usr/bin/env pwsh
# Installs the Souther command line on Windows from a GitHub Release, for the current user only.
#
#   irm https://raw.githubusercontent.com/souther-lang/souther/main/install.ps1 | iex
#
# Piping to iex passes no arguments, so the form that takes them names the script block:
#
#   & ([scriptblock]::Create((irm https://raw.githubusercontent.com/souther-lang/souther/main/install.ps1))) -Nojre
#   & ([scriptblock]::Create((irm https://raw.githubusercontent.com/souther-lang/souther/main/install.ps1))) -Uninstall

[CmdletBinding()]
param(
    # A release version without the `v`, or the latest release when left out.
    [string] $Version,
    # The distribution that expects a Java 25 on the machine rather than carrying one.
    [switch] $Nojre,
    [switch] $Uninstall,
    [string] $InstallDir = (Join-Path $env:LOCALAPPDATA 'Programs\souther')
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
[Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12

$repository = 'souther-lang/souther'

# Every entry this script ever adds is under the install directory, so taking all of them out is how
# both the uninstall and a reinstall onto a different distribution leave the variable with one entry.
function Set-UserPathEntry([string] $keep) {
    $current = [Environment]::GetEnvironmentVariable('Path', 'User')
    $entries = @()
    if ($current) { $entries = $current -split ';' | Where-Object { $_ } }
    $entries = $entries | Where-Object { -not $_.StartsWith($InstallDir, [StringComparison]::OrdinalIgnoreCase) }
    if ($keep) { $entries = @($entries) + $keep }
    [Environment]::SetEnvironmentVariable('Path', ($entries -join ';'), 'User')
}

# A junction is deleted as the link it is. Removing it the way a directory is removed reaches what
# it points at, which here is a directory under this one.
function Remove-Junction([string] $path) {
    if (Test-Path $path) { [IO.Directory]::Delete($path) }
}

if ($Uninstall) {
    Set-UserPathEntry $null
    Remove-Junction (Join-Path $InstallDir 'current')
    if (Test-Path $InstallDir) { Remove-Item -Recurse -Force $InstallDir }
    Write-Host 'souther is uninstalled. Open a new terminal for PATH to say so.'
    return
}

if (-not $Version) {
    $latest = Invoke-RestMethod "https://api.github.com/repos/$repository/releases/latest"
    $Version = $latest.tag_name -replace '^v', ''
}

$archive = if ($Nojre) { "souther-$Version-windows-x64-nojre.zip" } else { "souther-$Version-windows-x64.zip" }
$base = "https://github.com/$repository/releases/download/v$Version"

$work = Join-Path ([IO.Path]::GetTempPath()) ("souther-install-" + [Guid]::NewGuid())
New-Item -ItemType Directory -Force -Path $work | Out-Null
try {
    $zip = Join-Path $work $archive
    Write-Host "downloading $archive"
    Invoke-WebRequest "$base/$archive" -OutFile $zip
    Invoke-WebRequest "$base/SHA256SUMS" -OutFile (Join-Path $work 'SHA256SUMS')

    # The release publishes one sums file over all of its assets, so the line for this one is found
    # by name. An asset the file does not mention is not one this release published.
    $line = Get-Content (Join-Path $work 'SHA256SUMS') | Where-Object { $_ -match "\s$([Regex]::Escape($archive))$" }
    if (-not $line) { throw "SHA256SUMS for v$Version does not mention $archive" }
    $expected = ($line -split '\s+')[0]
    $actual = (Get-FileHash $zip -Algorithm SHA256).Hash
    if ($actual -ne $expected.ToUpperInvariant()) {
        throw "$archive hashes to $actual and the release says $expected"
    }

    # The archive holds a `souther` directory, and the installed version is that directory under a
    # name of its own, so more than one version can sit here and `current` can be pointed at any.
    $unpacked = Join-Path $work 'unpacked'
    Add-Type -AssemblyName System.IO.Compression.FileSystem
    [IO.Compression.ZipFile]::ExtractToDirectory($zip, $unpacked)

    $installed = Join-Path $InstallDir $Version
    $link = Join-Path $InstallDir 'current'
    Remove-Junction $link
    if (Test-Path $installed) { Remove-Item -Recurse -Force $installed }
    New-Item -ItemType Directory -Force -Path $InstallDir | Out-Null
    Move-Item (Join-Path $unpacked 'souther') $installed
    New-Item -ItemType Junction -Path $link -Target $installed | Out-Null
}
finally {
    Remove-Item -Recurse -Force $work -ErrorAction SilentlyContinue
}

# Where the launcher sits differs between the two distributions, and `current` is what keeps the
# entry the same across versions of either.
$bin = if ($Nojre) { Join-Path $link 'bin' } else { $link }
Set-UserPathEntry $bin

Write-Host "souther $Version is installed in $installed."
Write-Host "$bin is on your PATH. Open a new terminal, then run: souther help"
