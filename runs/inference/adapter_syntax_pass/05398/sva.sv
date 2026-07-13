module adder_16bit_signed_unsigned_sva (
    input logic signed [15:0] a,
    input logic signed [15:0] b,
    input logic cin,
    input logic signed [15:0] sum,
    input logic cout
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.

    // sum must match the RTL's selected adder result.
    check_sum_function: assert property (
        @($global_clock)
        sum == ((a[15] == b[15]) ? (a + b + cin) : ((a > b) ? (a + b) : (b + a)))
    );

    // cout must match the RTL's carry equation.
    check_cout_function: assert property (
        @($global_clock)
        cout == ((a[15] & b[15]) | ((a[15] | b[15]) & ~((a + b + cin)[15])))
    );

    // When the two inputs have the same sign, sum must be the unsigned result.
    check_same_sign_sum: assert property (
        @($global_clock)
        (a[15] == b[15]) |-> (sum == (a + b + cin))
    );

    // When the two inputs have different signs, sum must be the larger input plus cin.
    check_different_sign_sum: assert property (
        @($global_clock)
        (a[15] != b[15]) |-> (sum == ((a > b) ? (a + b) : (b + a)))
    );

    // When both inputs are non-negative, cout must be the unsigned carry-out.
    check_nonnegative_cout: assert property (
        @($global_clock)
        ((a[15] == 1'b0) && (b[15] == 1'b0)) |-> (cout == ((a + b + cin) > 16'h0000))
    );

    // When both inputs are non-positive, cout must be the unsigned carry-out.
    check_nonpositive_cout: assert property (
        @($global_clock)
        ((a[15] == 1'b1) && (b[15] == 1'b1)) |-> (cout == ((a + b + cin) > 16'h0000))
    );

    // When the inputs have opposite signs, cout must be the inverse of the unsigned MSB.
    check_mixed_sign_cout: assert property (
        @($global_clock)
        (a[15] != b[15]) |-> (cout == ~((a + b + cin)[15]))
    );

endmodule