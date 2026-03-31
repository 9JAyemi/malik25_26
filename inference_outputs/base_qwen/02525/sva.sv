```systemverilog
module digital_circuit_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1_N
);
    // No clock or reset signals are present in the RTL

    // Sequential logic is not present in the RTL

    // Combinational logic is present in the RTL

    // Key signals and interfaces:
    // - Y: Output of the digital circuit
    // - A1, A2: Inputs to the AND gate
    // - B1_N: Input to the NOT gate

    // Functional behaviors:
    // - The output Y is the result of a NOR gate followed by a buffer
    // - The NOR gate takes the output of a NOT gate and the output of an AND gate

    // Combinational logic assertion
    // The output Y should be the result of the NOR gate followed by a buffer
    comb_logic: assert property (
        @(posedge clk) disable iff (!RESETn) (Y == ~(~B1_N & A1 & A2))
    ) else $error("Combinational logic assertion failed");
endmodule
```