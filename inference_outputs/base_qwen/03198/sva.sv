```systemverilog
module full_adder_sva (
    input logic A,
    input logic B,
    input logic Ci,
    output logic S,
    output logic Co
);
    // Sequential logic is not present, so all assertions will be clocked.
    // No reset signal is present, so no disable iff clauses are needed.

    // Combinational logic: S is the sum of A, B, and Ci.
    sum_check: assert property (
        @(posedge clk) S == (A ^ B ^ Ci)
    ) else $error("Sum calculation is incorrect.");

    // Combinational logic: Co is the carry out of the full adder.
    carry_out_check: assert property (
        @(posedge clk) Co == ((A & B) | ((A ^ B) & Ci))
    ) else $error("Carry out calculation is incorrect.");

    // Combinational logic: S and Co cannot both be 1.
    no_overflow_check: assert property (
        @(posedge clk) !(S & Co)
    ) else $error("Overflow detected in full adder.");

endmodule
```