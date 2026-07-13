module ripple_carry_adder_sva #(
    parameter int n = 4
)(
    input logic clk,
    input logic [n-1:0] A,
    input logic [n-1:0] B,
    input logic [n-1:0] S
);
    ///// Functional correctness /////
    // S equals the n-bit sum of A and B (truncated modulo 2^n).
    check_sum_mod_n: assert property (
        @(posedge clk) S == (A + B)
    );

    // LSB sum has no carry-in: S[0] == A[0] ^ B[0].
    check_lsb_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0])
    );

    // If A is zero, S must equal B.
    check_identity_A_zero: assert property (
        @(posedge clk) (A == '0) |-> (S == B)
    );

    // If B is zero, S must equal A.
    check_identity_B_zero: assert property (
        @(posedge clk) (B == '0) |-> (S == A)
    );

    // With no overlapping 1s, addition reduces to bitwise OR.
    check_disjoint_inputs_or: assert property (
        @(posedge clk) ((A & B) == '0) |-> (S == (A | B))
    );

    // Equal operands sum to a left shift by 1 (modulo 2^n).
    check_equal_operands_shift: assert property (
        @(posedge clk) (A == B) |-> (S == (A << 1))
    );

    // Complementary operands sum to all ones (modulo 2^n).
    check_complementary_operands_all_ones: assert property (
        @(posedge clk) (B == ~A) |-> (S == {n{1'b1}})
    );

    ///// Local carry-in determinism from LSB /////
    // If A[0]=0 and B[0]=0, carry into bit1 is 0 so S[1]==A[1]^B[1].
    if (n > 1) begin : g_bit1_props
        check_bit1_xor_when_lsb_00: assert property (
            @(posedge clk) (A[0] == 1'b0 && B[0] == 1'b0) |-> (S[1] == (A[1] ^ B[1]))
        );
        // If A[0]=1 and B[0]=1, carry into bit1 is 1 so S[1]==~(A[1]^B[1]).
        check_bit1_xnor_when_lsb_11: assert property (
            @(posedge clk) (A[0] == 1'b1 && B[0] == 1'b1) |-> (S[1] == ~(A[1] ^ B[1]))
        );
    end

    ///// Higher-bit XOR when all lower bits are zero /////
    // For any i>0, if all lower bits of A and B are zero, carry-in to i is 0 so S[i]==A[i]^B[i].
    genvar i;
    generate
        for (i = 1; i < n; i++) begin : lower_zeros_imp_xor
            check_xor_when_lower_zeros: assert property (
                @(posedge clk) ((A[i-1:0] == '0) && (B[i-1:0] == '0)) |-> (S[i] == (A[i] ^ B[i]))
            );
        end
    endgenerate
endmodule