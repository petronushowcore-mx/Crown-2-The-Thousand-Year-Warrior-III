# The Thousand-Year Warrior III, or The Gathering Point

Author: **Maksim Barziankou (MxBv)**  
Affiliation: The Urgrund Laboratheory  
Contact: research@petronus.eu  

![Six figures of different ages stand in the foreground. A raised blade sways as translucent figures pass behind them.](thousand-year-warrior-iii-poster.webp)

[Static image (JPG)](thousand-year-warrior-iii-cover.jpg) | [MP4 animation](thousand-year-warrior-iii-poster.mp4)

## Scope and limits

The manuscript states its premises and limits. Its Python companion executes declared finite and exact models. The Lean sources cover the selected mathematical statements listed in their instructions; recorded compiler results concern earlier runs on those exact source bytes.

## Read and download

| File | Contents |
|---|---|
| [English manuscript](TYW-III-EN.md) | The exact English source |
| [Protected PDF](Thousand-Year-Warrior-III-EN-20261119.pdf) | The same work in PDF |
| [Standalone ZIP](warrior-iii-EN-companion-20261119.zip) | The complete autonomous companion |
| [Companion instructions](companion/README.md) | Model coverage and commands |
| [Lean instructions](companion/lean/README.md) | Formal sources and pinned dependencies |

The complete contents beneath the original ZIP top-level directory are preserved byte for byte in companion/. Its original README, source manifest and checksums remain intact.

## Run the companion

Python 3.10 or later and the standard library are sufficient for the Python checks. They make no network or model-provider calls. From the repository root:

```sh
cd companion
python harness.py --teeth
python break_harness.py
python deep/suite.py --work warrior --profile full --json deep-result.json
```

The companion README gives the full commands, including optimised Python. The deep layer has its own [instructions](companion/deep/README.md). Choose fresh output names when preserving results. Initial Lean dependency retrieval requires elan and network access; its toolchain and Mathlib revision are pinned in companion/lean/.

## Source locators

Paths in companion/deep/source-index.json are logical locators in the shared three-work layout. Only this work's manuscript is enclosed. References to the other works are pinned by hashes, quotations or span locators; those paths are not local file links. The Python models run independently of this index.

## Licences and integrity

The manuscript is licensed under [CC BY-NC-ND 4.0](https://creativecommons.org/licenses/by-nc-nd/4.0/). Code and usage instructions use the [MIT licence](companion/LICENSE-code.txt).

The root [SHA256SUMS](SHA256SUMS) records every payload file other than itself and detached signatures or timestamps. The original companion has its own preserved checksums. The [PETRONUS Research public key](PETRONUS-Research-public-key.asc) accompanies the files for signature verification.
