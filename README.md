Benchmarking Precision-Scalable MAC Units
=========================================

Introduction
------------

This repository contains supplementary materials and part of the sources
for the benchmarking study from:\
[V. Camus, L. Mei, C. Enz, and M. Verhelst, “Review and benchmarking
of precision-scalable multiply-accumulate unit architectures for
embedded neural-network processing,” in IEEE JETCAS, 2019.
](https://doi.org/10.1109/JETCAS.2019.2950386)

These files are shared as-is for educational and inspirational purposes.
They have not been cleaned up or prepared for use in any environment.
Enjoy the SystemVerilog, Tcl, and Perl!


Structure
---------

This repository features various precision-scalable or vector-scalable MAC
architectures, each in its **`mac_<architecture>`** folder. Each architecture
folder contains the necessary files for simulation, synthesis, and testing,
following a consistent structure:

- **`mac_<architecture>.sv`**: The main SystemVerilog that defines the generic MAC architecture's logic.
- **`assertions/`**: (Optional) Some architecture have assertion binding files for verification during testbenches and powerbenches.
- **`batch/`**: Contains the different parameterized or pre-built instanciations for each architecture, varying the level of scalability into a 
- **`batch/`**: Contains the parameterized or pre-configured architecture instances, varying the level of scalability. Implements a `top_mac_<architecture>` module that includes input registers, mode and configuration signals, and shareable sequencing logic, synthesized but excluded from power and area analysis.
- **`constraints/`**: Timing constraint files for each MAC instance. For each dynamic precision mode, unused registers and known static signals are declared to prevent STA from unnecessarily optimizing.
- **`pb/`**: Contains powerbench files used for post-synthesis simulation and power estimation for each MAC instance. The gate-level netlist is simulated with precision mode, clock frequency, stimuli and VCD files set by external parameters.
- **`tb_mac_<architecture>.sv`**: (Unused) Testbench manually set for debugging purposes, not used by the DSE framework.
- **`sim_tb_mac_<architecture>.tcl`**: (Unused) Automates testbench simulation launch, not used by the DSE framework.
- **`sim_pb_mac_<architecture>.tcl`**: Automates powerbench simulation setup and launch via Modelsim/Questa. It has both manual and automatic modes, the latter being activated during the DSE framework run (by a set ``AUTO`` variable).
- **`syn_mac_<architecture>.tcl`**: Synthesis script for Cadence Genus. It synthesizes the top_mac_<architecture> with a separate `mac` module, which does not contain the top-level input registers, configuration signals and shareable sequencing logic, that can be used for the core MAC architecture power estimation. The script reports the calculated effective throughput ratios, or operations per clock cycle for each precision mode (e.g. for SWP/multiplex architecture: 1 for 8b-8b/4b-8b/2b-8b, 2 for 4b-4b/2b-4b, 4 for 2b-2b), area, power estimates, as well as many specific timing slacks to understand the critical paths.



MAC architectures
-----------------

The following table maps the architecture names used in the paper to the
corresponding folder names in this repository:

| Paper architecture name                                  | Repository folder name |
|----------------------------------------------------------|------------------------|
| Data-gated conventional                                  | `mac_conventional`     |
| 1D Divide-and-Conquer SA (D&C SA, DNPU [13])             | `mac_dnc`              |
| 1D Divide-and-Conquer ST (D&C ST)                        | `mac_bfusion1d`        |
| 2D Divide-and-Conquer SA (D&C SA)                        | `mac_bitseparation`    |
| 2D Divide-and-Conquer ST (D&C ST, BitFusion [14])        | `mac_bfusion`          |
| Subword-Parallel SA (SWP SA, DVAFS [15])                 | `mac_multiplex`        |
| Subword-Parallel ST (SWP ST, Sum-Together [16])          | `mac_st`               |
| 1D Bit/Multibit serial (UNPU [17], Multibit serial [18]) | `mac_serial`           |
| 2D Bit/Multibit serial (LOOM [19])                       | `mac_serial2d`         |