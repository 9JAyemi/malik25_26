# Veri2: A Formally Verified RTL–SVA Dataset for Fine-Tuning Local Language Models

## Overview

Veri2 is a synthetic RTL–SVA dataset created through knowledge distillation from GPT-5 and filtered using a two-stage Cadence JasperGold verification pipeline. The project investigates whether formally verified training data can improve SystemVerilog Assertion (SVA) generation compared to larger but noisier datasets.

The repository contains:

* Dataset generation scripts
* GPT-5 batch API generation infrastructure
* Fine-tuning and inference code
* Model inference outputs and adapter-training notebooks
* Three Veri2 dataset tiers
* Evaluation artifacts used in the paper

The central hypothesis explored in this work is that **data quality outweighs data quantity** for SVA generation. Models trained on formally verified assertions consistently outperform models trained on substantially larger unfiltered datasets.

---

## Repository Structure

```text
.
├── data/veri_thoughts/
│   ├── generated/          # 5,774 cumulative RTL–SVA pairs
│   ├── prepared/           # all, syntax_pass, and verified JSONL splits
│   └── filters/
├── notebooks/              # QLoRA training and vLLM inference
├── scripts/                # generation, JasperGold, preparation, and analysis
├── runs/
│   ├── generation/
│   ├── formal/
│   └── inference/
├── reports/                # derived CSV, PNG, and HTML results
├── experiments/            # VERT, GPT baselines, and distillation studies
└── docs/reference/         # JasperGold error reference material
```

### `notebooks/`

Contains all code required for training and inference of QLoRA adapters.

Includes:

* Dataset preprocessing
* Training scripts
* QLoRA configuration
* Inference scripts
* Evaluation utilities

Adapters are trained on Qwen2.5-Coder-7B-Instruct using the dataset variants described below.

---

### `scripts/`

Contains the GPT-5 generation infrastructure, JasperGold runners, dataset
preparation, and evaluation utilities.

Includes:

* OpenAI Batch API request creation
* JSONL generation
* Batch submission scripts
* Result retrieval
* Output post-processing

These scripts were used to generate assertions from RTL modules prior to verification filtering.

---

### `runs/inference/`

Contains inference outputs for all evaluated models.

Examples include:

* Base Qwen
* GPT-5 Baseline
* Adapter (All)
* Adapter (Syntax Pass)
* Adapter (Verified)
* Adapter (VERT)

These outputs are used for downstream JasperGold evaluation.

---

### `runs/formal/`

Contains syntax and formal-verification outputs from JasperGold. Canonical
VeriThoughts results live under `runs/formal/veri_thoughts`; model-evaluation
results live beside the inference conditions in `runs/inference`.

---

### `data/veri_thoughts/`

Contains the cumulative Veri2 dataset. Earlier `version_1` and `version_2`
directories represented cumulative snapshots; they have been collapsed into
the single `generated/` directory. Per-sample `source_version` metadata is
retained only for provenance.

The dataset is organized into three quality tiers:

| Tier        | Description                                            |
| ----------- | ------------------------------------------------------ |
| All         | All GPT-5 generated RTL–SVA pairs                      |
| Syntax Pass | Only pairs passing JasperGold syntax validation        |
| Verified    | Only pairs passing both syntax and formal verification |

Dataset statistics:

| Tier        | Modules | Assertions |
| ----------- | ------- | ---------- |
| All         | 5,774   | 45,451     |
| Syntax Pass | 5,412   | 42,125     |
| Verified    | 2,954   | 18,494     |

---

## Dataset Construction

Veri2 is created using the following workflow:

1. Select verified RTL modules from VeriThoughts.
2. Generate assertions using GPT-5.
3. Run JasperGold syntax validation.
4. Run JasperGold formal verification.
5. Retain passing assertions for the verified dataset tier.

This process produces progressively higher-quality subsets that can be used to study the effect of training data quality on downstream SVA generation.

---

## Fine-Tuning

All adapters were trained using QLoRA on Qwen2.5-Coder-7B-Instruct.

### Key Hyperparameters

| Parameter            | Value |
| -------------------- | ----- |
| LoRA Rank            | 64    |
| LoRA Alpha           | 128   |
| Epochs               | 3     |
| Effective Batch Size | 16    |
| Learning Rate        | 2e-4  |
| Max Sequence Length  | 8192  |

---

## Evaluation

Models are evaluated using a multi-stage verification pipeline:

1. Assertion generation
2. Syntax validation
3. RTL elaboration / binding
4. Formal verification

### Primary Metric

**Yield** = Percentage of generated assertions that are formally proven by JasperGold.

The strongest-performing adapter is trained on the **Verified** dataset tier and achieves higher assertion yield than both the GPT-5 teacher model and models trained on larger, lower-quality datasets.

---

## Reproducibility

Create a Python 3.10+ environment and install the appropriate dependency group:

```bash
python -m pip install -e .
python -m pip install -e '.[training]'   # QLoRA notebook
python -m pip install -e '.[inference]'  # vLLM notebook
```

Copy `.env.example` to `.env` and add credentials locally when generation or
Hugging Face access requires them. Then:

1. Generate assertions with `python scripts/generate_sva.py --batch`.
2. Run syntax and verification checks:

   ```bash
   scripts/check_all.sh syntax data/veri_thoughts/generated
   scripts/check_all.sh verif data/veri_thoughts/generated
   ```

3. Rebuild the three tiers with `python scripts/prepare_dataset.py`.
4. Run `notebooks/sva_qlora_finetune.ipynb` from the repository root.
5. Run `notebooks/sva_inference.ipynb` from the repository root.
6. Re-evaluate outputs with `scripts/run_check_all.sbatch` and rebuild reports
   with `python scripts/dataset_stats.py`.

---

## License

This repository is provided solely for anonymous artifact evaluation
associated with the submitted manuscript. Redistribution and public
release policies will be finalized upon publication.
