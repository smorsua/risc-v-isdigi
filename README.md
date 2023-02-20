# RISC-V Microprocessor Project
The RISC-V microprocessor project was developed by a team consisting of Mario Rico, Laura Rivero, Sergio Moreno Suay, Carolina García, and Luis Garrido. The project was developed in SystemVerilog and followed a roadmap consisting of four distinct phases.

## Phase 1
In the first phase, the team designed and validated the functional units of the processor, including:

Instruction and data memories
Register file
Arithmetic logic unit (ALU)
They also delved into the RISC-V architecture's programming model and created simple programs that could be used as benchmarks or test stimuli for the processor.

## Phase 2
The second phase consisted of implementing a single-cycle model of the processor. The priority was for the model to be completely functional. The model created in this phase was exhaustively validated and served as a golden model for the subsequent verification of the segmented implementation.

## Phase 3
The third phase aimed to segment the processor developed in the previous phase and introduce mechanisms for the detection and control of hazards that would enable the execution of the implemented instructions without introducing delay gaps or performing segmentation stops. The resulting processor had to be validated again using the single-cycle processor as a golden model.

## Phase 4
In the final phase, the team tackled the design of the microcontroller and hardware validation of the design by implementing it in the Cyclone IV FPGA modules available in the lab. The objective was to create a program that would run on the microcontroller and, using the elements available in the DE-2 module, carry out a simple application such as LED control, timing, or the use of 7-segment displays. The program created had to allow interaction with the user (i.e., it had to use both the GPIO module's output and input pins).

Throughout the project, the team gained valuable experience in using Git for version control, working collaboratively and effectively as a team, and project management.

In conclusion, the RISC-V microprocessor project was successfully developed by the team, and they were able to achieve all of their goals within the designated timeline. The project demonstrated the team's proficiency in SystemVerilog and FPGA implementation, as well as their ability to design and validate a functional microprocessor. Overall, the project was a great success, and the team's efforts will undoubtedly be of great value in their future endeavors.
