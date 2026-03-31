module adder_16bit_signed_unsigned_sva (
    input logic clk,
    input logic signed [15:0] a,
    input logic signed [15:0] b,
    input logic cin,
    input logic signed [15:0] sum,
    input logic cout
);

// sum must match the RTL's conditional select of the two addition results.
    check_sum_function: assert property (
        @(posedge clk) sum == ((a[15] == b[15]) ? unsigned_sum : (a > b) ? a_plus_b : b_plus_a)
    );

// When a and b have the same sign, sum must equal the unsigned sum.
    check_sum_same_sign: assert property (
        @(posedge clk) (a[15] == b[15]) |-> (sum == unsigned_sum)
    );

// When a and b have different signs, sum must equal the larger absolute value.
    check_sum_different_sign: assert property (
        @(posedge clk) (a[15] != b[15]) |-> (sum == (a > b) ? a_plus_b : b_plus_a)
    );

// When a and b have different signs and a is greater, sum must equal a_plus_b.
    check_sum_different_sign_a_greater: assert property (
        @(posedge clk) (a[15] != b[15] && a > b) |-> (sum == a_plus_b)
    );

// When a and b have different signs and b is greater, sum must equal b_plus_a.
    check_sum_different_sign_b_greater: assert property (
        @(posedge clk) (a[15] != b[15] && b > a) |-> (sum == b_plus_a)
    );

// cout must match the RTL's carry equation.
    check_cout_equation: assert property (
        @(posedge clk) cout == ((a[15] & b[15]) | ((a[15] | b[15]) & ~unsigned_sum[15]))
    );

// If both operands are non-negative, cout must equal the unsigned carry.
    check_cout_nonnegative_inputs: assert property (
        @(posedge clk) (a >= 0 && b >= 0) |-> (cout == unsigned_cout)
    );

// If both operands are non-positive, cout must equal the unsigned carry.
    check_cout_nonpositive_inputs: assert property (
        @(posedge clk) (a <= 0 && b <= 0) |-> (cout == unsigned_cout)
    );

// If a is non-negative and b is non-positive, cout must be low.
    check_cout_mixed_sign_negative_a_positive_b: assert property (
        @(posedge clk) (a >= 0 && b <= 0) |-> (cout == 1'b0)
    );

// If a is non-positive and b is non-negative, cout must be low.
    check_cout_mixed_sign_negative_b_positive_a: assert property (
        @(posedge clk) (a <= 0 && b >= 0) |-> (cout == 1'b0)
    );

endmodule
