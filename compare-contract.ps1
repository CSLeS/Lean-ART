param(
    [Parameter(Mandatory = $true)][string]$Original,
    [string]$CompletedDirectory = (Split-Path -Parent $PSScriptRoot)
)
$ErrorActionPreference = 'Stop'
$originalText = (Get-Content -LiteralPath $Original -Raw).Replace("`r`n", "`n")
$baseText = (Get-Content -LiteralPath (Join-Path $CompletedDirectory 'AnthropicRepresentation\Basic.lean') -Raw).Replace("`r`n", "`n")
$entryText = (Get-Content -LiteralPath (Join-Path $CompletedDirectory 'AnthropicRepresentation.lean') -Raw).Replace("`r`n", "`n")

function Get-ContractBlock([string]$Text, [string]$Start, [string]$End) {
    $startIndex = $Text.IndexOf($Start)
    $endIndex = $Text.IndexOf($End, $startIndex)
    if ($startIndex -lt 0 -or $endIndex -lt 0) { throw 'Missing contract boundary' }
    return $Text.Substring($startIndex, $endIndex - $startIndex).Trim()
}

$coreEqual = (Get-ContractBlock $originalText 'set_option autoImplicit false' '/-! ## Supporting lemmas') -ceq
    (Get-ContractBlock $baseText 'set_option autoImplicit false' 'end Abstract')
$paperEqual = (Get-ContractBlock $originalText '/-! ## Problem / information-set / action adapter' '/-! ## Final audit') -ceq
    (Get-ContractBlock $entryText '/-! ## Problem / information-set / action adapter' '/-! Kernel dependency audit')
$delibEqual = (Get-ContractBlock $originalText '/-- Deliberation:' '/-- Theorem 1, "moreover": each') -ceq
    (Get-ContractBlock $entryText '/-- Deliberation:' 'end Abstract')

[PSCustomObject]@{
    ProtectedCoreDefinitionsIdentical = $coreEqual
    PaperAdapterIdentical = $paperEqual
    DelibAndVIdentical = $delibEqual
    InputSHA256 = (Get-FileHash -LiteralPath $Original -Algorithm SHA256).Hash
} | Format-List
if (-not ($coreEqual -and $paperEqual -and $delibEqual)) { throw 'Contract comparison failed' }
