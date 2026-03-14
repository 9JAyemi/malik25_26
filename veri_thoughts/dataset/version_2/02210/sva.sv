module ripple_carry_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] sum,
    input logic       carry_out
);
    // Use the only edge in the RTL (posedge carry_out) as the property clock.
    default clocking @(posedge carry_out); endclocking

    // Rising edge cannot occur when both inputs are zero.
    check_no_rise_when_inputs_zero: assert property (
        (A != 4'd0) || (B != 4'd0)
    );

    // If A+B < 16, on a rise of carry_out the 4-bit sum must be strictly less than A+B.
    check_sum_lt_ab_when_ab_lt16: assert property (
        (({1'b0, A} + {1'b0, B}) < 5'd16) |-> ({1'b0, sum} < ({1'b0, A} + {1'b0, B}))
    );

    // If A+B >= 16, on a rise of carry_out the 4-bit sum must be at least (A+B - 16).
    check_sum_ge_ab_minus16_when_ab_ge16: assert property (
        (({1'b0, A} + {1'b0, B}) >= 5'd16) |-> ({1'b0, sum} >= (({1'b0, A} + {1'b0, B}) - 5'd16))
    );

    // When A+B == 31, on a rise of carry_out the sum must be 15.
    check_sum_eq_15_when_ab_eq31: assert property (
        (({1'b0, A} + {1'b0, B}) == 5'd31) |-> (sum == 4'd15)
    );

    // On a rise of carry_out, the 4-bit sum can never exceed A+B.
    check_sum_never_exceeds_ab_on_rise: assert property (
        ({1'b0, sum} <= ({1'b0, A} + {1'b0, B}))
    );

    // When A+B == 1, on a rise of carry_out the sum must be 0.
    check_sum_zero_when_ab_eq1_on_rise: assert property (
        (({1'b0, A} + {1'b0, B}) == 5'd1) |-> (sum == 4'd0)
    );

    // When A==15 and B==15, on a rise of carry_out the sum must be at least 14.
    check_lower_bound_for_max_inputs_on_rise: assert property (
        (A == 4'd15 && B == 4'd15) |-> (sum >= 4'd14)
    );

    // When A+B == 15, on a rise of carry_out the sum must be <= 14.
    check_sum_le_14_when_ab_eq15_on_rise: assert property (
        (({1'b0, A} + {1'b0, B}) == 5'd15) |-> (sum <= 4'd14)
    );

endmodule