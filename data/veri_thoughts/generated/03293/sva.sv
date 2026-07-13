module multiplier_divider_assertions (
    input logic [3:0] in,
    input logic [3:0] out
);

    // Inputs 0 through 4 take the multiply-by-two branch.
    check_multiply_branch: assert property (
        @($global_clock)
        (in <= 4'd4) |-> (out == (in << 1))
    );

    // Inputs above 4 take the divide-by-two branch.
    check_divide_branch: assert property (
        @($global_clock)
        (in > 4'd4) |-> (out == (in >> 1))
    );

    // Input 4 is included in the multiply-by-two condition.
    check_boundary_at_four: assert property (
        @($global_clock)
        (in == 4'd4) |-> (out == 4'd8)
    );

    // Input 5 is the first value that uses divide-by-two.
    check_boundary_at_five: assert property (
        @($global_clock)
        (in == 4'd5) |-> (out == 4'd2)
    );

endmodule