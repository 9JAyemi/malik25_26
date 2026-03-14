module nand_full_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] sum,
    input logic [3:0] xor1_out,
    input logic [3:0] xor2_out,
    input logic [3:0] and1_out,
    input logic [3:0] and2_out,
    input logic [3:0] and3_out,
    input logic [3:0] or1_out
);
    // No clock/reset in DUT; assertions are sampled on external clk.
    // Purely combinational logic wiring: xor/and/or nets and final sum.

    // xor1_out equals A XOR B.
    check_xor1_definition: assert property (
        @(posedge clk) xor1_out == (A ^ B)
    );

    // xor2_out equals xor1_out XOR C.
    check_xor2_definition: assert property (
        @(posedge clk) xor2_out == (xor1_out ^ C)
    );

    // and1_out equals A AND B.
    check_and1_definition: assert property (
        @(posedge clk) and1_out == (A & B)
    );

    // and2_out equals xor1_out AND C.
    check_and2_definition: assert property (
        @(posedge clk) and2_out == (xor1_out & C)
    );

    // and3_out equals and1_out AND C.
    check_and3_definition: assert property (
        @(posedge clk) and3_out == (and1_out & C)
    );

    // or1_out equals and2_out OR and3_out.
    check_or1_definition: assert property (
        @(posedge clk) or1_out == (and2_out | and3_out)
    );

    // or1_out simplifies to C AND (A OR B).
    check_or1_simplified: assert property (
        @(posedge clk) or1_out == (C & (A | B))
    );

    // or1_out is masked by C (no bit set where C bit is 0).
    check_or1_masked_by_C: assert property (
        @(posedge clk) ((or1_out & ~C) == 4'b0000)
    );

    // and2_out and and3_out are mutually exclusive per bit.
    check_and2_and3_disjoint: assert property (
        @(posedge clk) ((and2_out & and3_out) == 4'b0000)
    );

    // sum equals or1_out XOR xor2_out.
    check_sum_definition: assert property (
        @(posedge clk) sum == (or1_out ^ xor2_out)
    );

    // sum expressed only with primary inputs.
    check_sum_inputs_only: assert property (
        @(posedge clk) sum == (((A | B) & C) ^ (A ^ B ^ C))
    );

    // When A, B, and C are equal bitwise, sum is all zeros.
    check_sum_zero_when_all_equal: assert property (
        @(posedge clk) ((A == B) && (B == C)) |-> (sum == 4'b0000)
    );

    // When C is all zeros, sum reduces to A XOR B.
    check_sum_when_C_zero: assert property (
        @(posedge clk) (C == 4'b0000) |-> (sum == (A ^ B))
    );

    // When C is all ones, or1_out equals A OR B.
    check_or1_when_C_allones: assert property (
        @(posedge clk) (C == 4'hF) |-> (or1_out == (A | B))
    );

    // When C is all ones, sum equals (A OR B) XOR NOT (A XOR B).
    check_sum_when_C_allones: assert property (
        @(posedge clk) (C == 4'hF) |-> (sum == ((A | B) ^ ~(A ^ B)))
    );

endmodule