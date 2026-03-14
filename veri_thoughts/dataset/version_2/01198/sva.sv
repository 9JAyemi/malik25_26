module four_bit_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [4:0] S,
    input logic [3:0] sum,
    input logic       carry_out
);
    ///// Structural wiring checks /////
    // S equals the concatenation of carry_out and sum.
    check_S_is_concat: assert property (
        @(posedge CLK) S == {carry_out, sum}
    );

    // sum equals the lower 4 bits of S.
    check_sum_matches_S: assert property (
        @(posedge CLK) sum == S[3:0]
    );

    // carry_out equals the MSB of S.
    check_carry_matches_S: assert property (
        @(posedge CLK) carry_out == S[4]
    );

    ///// Functional equivalence to addition /////
    // Internal concatenation equals A + B.
    check_concat_equals_add: assert property (
        @(posedge CLK) {carry_out, sum} == (A + B)
    );

    // S equals A + B.
    check_S_equals_add: assert property (
        @(posedge CLK) S == (A + B)
    );

    ///// Value range and carry behavior /////
    // S is within 0..30 for 4-bit A and B.
    check_S_range: assert property (
        @(posedge CLK) S <= 5'd30
    );

    // Carry is set when A + B exceeds 15.
    check_carry_when_overflow: assert property (
        @(posedge CLK) ((A + B) > 5'd15) |-> (carry_out == 1'b1)
    );

    // No carry when A + B does not exceed 15.
    check_no_carry_when_not_overflow: assert property (
        @(posedge CLK) ((A + B) <= 5'd15) |-> (carry_out == 1'b0)
    );

    ///// Stability property /////
    // Output S is stable when A and B are stable.
    check_stable_output_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(B)) |-> $stable(S)
    );

    ///// Simple corner case /////
    // Zero inputs produce zero output and no carry.
    check_zero_inputs_zero_output: assert property (
        @(posedge CLK) ((A == 4'd0) && (B == 4'd0)) |-> (S == 5'd0)
    );
endmodule