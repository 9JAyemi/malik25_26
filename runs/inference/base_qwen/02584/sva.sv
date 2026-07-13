module four_bit_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Ci,
    input logic [3:0] S,
    input logic Co
);
    // Full adder logic is combinational, but we will use clocked assertions for consistency.

    // Ci can only transition from HIGH to LOW when all bits of A and B are LOW.
    ci_transition: assert property (
        @(posedge CLK) disable iff (!CLK) $fell(Ci) |-> (A == 4'b0000) && (B == 4'b0000)
    );

    // S[0] is the sum of A[0] and B[0] with Ci.
    sum_0: assert property (
        @(posedge CLK) disable iff (!CLK) S[0] == (A[0] ^ B[0] ^ Ci)
    );

    // S[1] is the sum of A[1] and B[1] with carry from S[0].
    sum_1: assert property (
        @(posedge CLK) disable iff (!CLK) S[1] == (A[1] ^ B[1] ^ S[0])
    );

    // S[2] is the sum of A[2] and B[2] with carry from S[1].
    sum_2: assert property (
        @(posedge CLK) disable iff (!CLK) S[2] == (A[2] ^ B[2] ^ S[1])
    );

    // S[3] is the sum of A[3] and B[3] with carry from S[2].
    sum_3: assert property (
        @(posedge CLK) disable iff (!CLK) S[3] == (A[3] ^ B[3] ^ S[2])
    );

    // Co is the carry out from the last full adder.
    carry_out: assert property (
        @(posedge CLK) disable iff (!CLK) Co == (A[3] & B[3] | A[3] & S[2] | B[3] & S[2])
    );
endmodule