module ripple_carry_adder_sva #(
    parameter int n = 4
)(
    input  logic                 clk,  // sampling clock for SVA (DUT is combinational)
    input  logic [n-1:0]         A,
    input  logic [n-1:0]         B,
    input  logic [n:0]           C
);
    ///// Functional equivalence /////
    // C equals zero-extended sum of A and B.
    check_full_sum_correct: assert property (
        @(posedge clk) disable iff (1'b0) C == ({1'b0, A} + {1'b0, B})
    );

    // MSB carry equals MSB of the zero-extended addition.
    check_msb_carry_bit: assert property (
        @(posedge clk) disable iff (1'b0) C[n] == (({1'b0, A} + {1'b0, B})[n])
    );

    ///// Bit-level consequences /////
    // LSB sum is XOR since carry-in is 0.
    check_lsb_sum: assert property (
        @(posedge clk) disable iff (1'b0) C[0] == (A[0] ^ B[0])
    );

    // Carry into bit1 equals A[0] & B[0] (only if bit1 exists).
    generate if (n >= 1) begin : have_bit1
        check_carry1_from_lsb: assert property (
            @(posedge clk) disable iff (1'b0) C[1] == (A[0] & B[0])
        );
    end endgenerate

    // For each prefix, low (i+1) sum bits match truncated addition.
    generate
        genvar i;
        for (i = 0; i < n; i = i + 1) begin : gen_lower_partial_sum
            check_lower_partial_sum: assert property (
                @(posedge clk) disable iff (1'b0) C[i:0] == (A[i:0] + B[i:0])
            );
        end
    endgenerate

    // Bit j equals XOR of A[j], B[j], and carry-in from lower bits.
    generate
        genvar j;
        for (j = 1; j < n; j = j + 1) begin : gen_bit_sum_with_carry_in
            check_bit_sum_with_carry_in: assert property (
                @(posedge clk) disable iff (1'b0)
                    C[j] == ((A[j] ^ B[j]) ^ (({1'b0, A[j-1:0]} + {1'b0, B[j-1:0]})[j]))
            );
        end
    endgenerate

    ///// Special operand cases /////
    // If A is zero, C passes through B (zero-extended).
    check_zero_a_passthrough: assert property (
        @(posedge clk) disable iff (1'b0) (A == '0) |-> (C == {1'b0, B})
    );

    // If B is zero, C passes through A (zero-extended).
    check_zero_b_passthrough: assert property (
        @(posedge clk) disable iff (1'b0) (B == '0) |-> (C == {1'b0, A})
    );

    // If A == B, result equals 2*A (zero-extended then left-shifted).
    check_doubling_when_equal: assert property (
        @(posedge clk) disable iff (1'b0) (A == B) |-> (C == ({1'b0, A} << 1))
    );

    // If B is bitwise NOT of A, sum is all ones with no carry-out.
    check_complement_all_ones: assert property (
        @(posedge clk) disable iff (1'b0) (B == ~A) |-> (C == {1'b0, {n{1'b1}}})
    );

    ///// Stability /////
    // With stable inputs across cycles, the output remains stable (combinational determinism).
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0) ($stable(A) && $stable(B)) |-> $stable(C)
    );
endmodule