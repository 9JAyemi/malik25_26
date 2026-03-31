```systemverilog
module ripple_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    output logic [3:0] S,
    output logic Cout
);
    // Sequential logic is not present in this module, so all logic is combinational.
    // However, we will still use @(posedge clk) to adhere to the guideline.

    // Full adder logic correctness
    // S[i] should be the sum of A[i], B[i], and Cin
    adder_0: assert property (
        @(posedge clk) disable iff (!reset_n) (S[0] == A[0] + B[0] + Cin)
    );
    adder_1: assert property (
        @(posedge clk) disable iff (!reset_n) (S[1] == A[1] + B[1] + Cin)
    );
    adder_2: assert property (
        @(posedge clk) disable iff (!reset_n) (S[2] == A[2] + B[2] + Cin)
    );
    adder_3: assert property (
        @(posedge clk) disable iff (!reset_n) (S[3] == A[3] + B[3] + Cin)
    );

    // Carry propagation correctness
    // Cout should be the carry out of the last full adder
    carry_out: assert property (
        @(posedge clk) disable iff (!reset_n) (Cout == (A[3] & B[3]) | (A[3] & Cin) | (B[3] & Cin))
    );

    // Cin should not be used after the last full adder
    cin_usage: assert property (
        @(posedge clk) disable iff (!reset_n) (Cin == 1'b0)
    );

    // S should not be used before the first full adder
    s_usage: assert property (
        @(posedge clk) disable iff (!reset_n) (S[0] == 4'b0)
    );

    // Reset behavior
    // At reset, S and Cout should be 0
    reset_s: assert property (
        @(posedge clk) !reset_n |-> (S == 4'b0)
    );
    reset_cout: assert property (
        @(posedge clk) !reset_n |-> (Cout == 1'b0)
    );

    // Reset polarity is active low
    parameter reset_n = 1'b0;
endmodule
```