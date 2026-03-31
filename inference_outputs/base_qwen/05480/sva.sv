```systemverilog
module adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    output logic [3:0] C,
    output logic CO
);
    // No clock or reset signals present in the RTL

    // Combinational logic: C and CO are determined by A and B
    // C should be the lower 4 bits of the sum of A and B
    comb_C: assert property (
        @(posedge clk) disable iff (!RESETn) (C == (A + B)[3:0])
    );

    // CO should be the carry-out bit of the sum of A and B
    comb_CO: assert property (
        @(posedge clk) disable iff (!RESETn) (CO == (A + B)[4])
    );
endmodule
```