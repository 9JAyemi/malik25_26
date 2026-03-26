module full_adder_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c_in,
    input logic sum,
    input logic c_out
);

    // Sum matches the three-input XOR of the inputs.
    check_sum_xor_function: assert property (
        @(posedge clk) sum == (a ^ b ^ c_in)
    );

    // Carry-out is high when at least two inputs are high.
    check_carry_majority_function: assert property (
        @(posedge clk) c_out == ((a & b) | (a & c_in) | (b & c_in))
    );

    // The two output bits encode the arithmetic sum of the three inputs.
    check_arithmetic_encoding: assert property (
        @(posedge clk) {c_out, sum} == ({1'b0, a} + {1'b0, b} + {1'b0, c_in})
    );

    // Zero inputs produce zero sum and zero carry.
    check_all_zero_case: assert property (
        @(posedge clk) (!a && !b && !c_in) |-> (!sum && !c_out)
    );

    // Exactly one high input produces sum high and carry low.
    check_single_one_case: assert property (
        @(posedge clk) $onehot({a, b, c_in}) |-> (sum && !c_out)
    );

    // Exactly two high inputs produce sum low and carry high.
    check_two_ones_case: assert property (
        @(posedge clk) $onehot({~a, ~b, ~c_in}) |-> (!sum && c_out)
    );

    // All high inputs produce sum high and carry high.
    check_all_one_case: assert property (
        @(posedge clk) (a && b && c_in) |-> (sum && c_out)
    );

    // With c_in low, the full adder reduces to a half adder on a and b.
    check_no_cin_half_adder_behavior: assert property (
        @(posedge clk) (!c_in) |-> ((sum == (a ^ b)) && (c_out == (a & b)))
    );

    // With a low, the full adder reduces to a half adder on b and c_in.
    check_a_zero_reduction: assert property (
        @(posedge clk) (!a) |-> ((sum == (b ^ c_in)) && (c_out == (b & c_in)))
    );

    // With b low, the full adder reduces to a half adder on a and c_in.
    check_b_zero_reduction: assert property (
        @(posedge clk) (!b) |-> ((sum == (a ^ c_in)) && (c_out == (a & c_in)))
    );

endmodule