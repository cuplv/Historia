# Artifact Submission Template

Please answer the following questions concisely, either with bullet lists or short paragraphs.

Title of the submitted paper:

**Discovery and Explanation of Event-Driven Defects with History-Aware Incorrectness Logic**

ECOOP submission number for the paper: **303**

## Metadata to provide during artifact submission in HotCRP

**No need to provide them again in the submission**

- OS and resource (CPU, memory, disk, GPU) used by the authors to run the artifact
- Estimation of the required hardware resources for evaluation. In case the evaluation takes multiple days or requires huge resources, please provide a scaled-down evaluation.
- Known compatibility issues of the container/VM.
- Which badges do you claim for your artifact? Functional? Reusable? Available?

## Quick-start guide (Kick-the-tires phase)

Please describe how reviewers can check the artifact's integrity and basic functionality.

TODO####!!!!!: test these on a different machine before submitting artifact.

There are two docker containers, one for Wistoria and another for the Infer/Pulse comparison. 
Separation of these containers was done to avoid dependency conflicts.
Please test that both are working using the following instructions:

### Wistoria

In order to test the artifact, load the docker containers using the commands `docker load < wistoria_docker.tgz`. 
Run the docker container using `docker run -p 8888:8888 -it wistoria_docker bash`.
Open a web browser to http://localhost:8888/lab/tree/reachExpGPT which should show Jupyter lab.
Open the notebook `ReachExpGPT.ipynb` and select the kernel menu at the top of the page then select restart and run all cells.
That is `Kernel -> Restart Kernel and Run All Cells...`.
This runs the experiments and should take less than 5 minutes to run.
Near the bottom, there is a header "Table 3 Producing Realistic Execution Histories" and underneath should be table 3 from the paper.

### Infer Comparison

Similar to the previous instructions, load the infer comparison container with `docker load < wistoria_infer_comparison.tgz`.

TODO####!!!!  add instructions here once c has script

## Overview: What does the artifact comprise?

Please list for each distinct component of your artifact:

* type of artifact (data, code, proof, etc.)
* format (e.g., CSV, source code, binary, etc.)
* location in the container/VM

## For authors claiming an available badge

We offer to publish the artifact on [DARTS](https://drops.dagstuhl.de/opus/institut_darts.php), in which case the available badge will be issued automatically.
If you agree to publishing your artifact under a Creative Commons license, please indicate this here.

**We agree to publish the artifact under a creative commons license.**

In case you would like to publish your artifact under different licensing conditions on Zenodo, please state under which license will the artifact be published?

## For authors claiming a functional or reusable badge

For **all** experimental claims made in the paper, please:
* Quote/reference the experimental claim
* Explain how this claim can be reproduced with the artifact

For example: “The data in table 1 can be obtained by running script ‘generate_table1.sh’”

Please note: we highly advise authors to provide a push-button evaluation (cf. call for artifacts).

## For authors claiming a reusable badge

If some parts of your artifacts contains software:
- is your implementation open-source?
- how to recompile the software?

If you use benchmarks: are the benchmarks public and open-source?

Please list any reuse scenarios that you envision for your artifact, i.e., state how the artifact can be reused or repurposed beyond its role in the submitted paper. Example:

* “The implementation can easily be modified to use a different algorithm than the one described in section 4.1 of our paper by implementing a corresponding module. We provide an interface specification in ...”
