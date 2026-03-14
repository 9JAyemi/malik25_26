module adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] Z
);
    ///// Functional behavior /////
    // Z equals the 4-bit sum modulo 10.
    check_mod10_behavior: assert property (
        @(posedge CLK) Z == ((A + B) % 4'd10)
    );

    // When 4-bit sum <= 9, Z equals the sum.
    check_pass_through_when_sum_le_9: assert property (
        @(posedge CLK) ((A + B) <= 4'd9) |-> (Z == (A + B))
    );

    // When 4-bit sum >= 10, Z equals sum - 10.
    check_subtract10_when_sum_ge10: assert property (
        @(posedge CLK) ((A + B) >= 4'd10) |-> (Z == ((A + B) - 4'd10))
    );

    // Z is always a decimal digit in the range 0..9.
    check_output_in_range_0_to_9: assert property (
        @(posedge CLK) (Z <= 4'd9)
    );

    // For 4-bit sums 10..15, Z must be in 0..5.
    check_remainder_bound_high_sums: assert property (
        @(posedge CLK) ((A + B) >= 4'd10) |-> (Z <= 4'd5)
    );

    // If inputs are unchanged cycle-to-cycle, output is unchanged.
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) (A == $past(A) && B == $past(B)) |-> (Z == $past(Z))
    );

    // If the 4-bit sum is unchanged, Z is unchanged.
    check_stability_when_sum_stable: assert property (
        @(posedge CLK) ((A + B) == $past(A + B)) |-> (Z == $past(Z))
    );

    // Corner case: 4-bit sum == 10 -> Z == 0.
    check_case_sum_eq_10: assert property (
        @(posedge CLK) ((A + B) == 4'd10) |-> (Z == 4'd0)
    );

    // Corner case: 4-bit sum == 15 -> Z == 5.
    check_case_sum_eq_15: assert property (
        @(posedge CLK) ((A + B) == 4'd15) |-> (Z == 4'd5)
    );

    // Corner case: 4-bit sum == 0 -> Z == 0.
    check_case_sum_eq_0: assert property (
        @(posedge CLK) ((A + B) == 4'd0) |-> (Z == 4'd0)
    );
endmodule