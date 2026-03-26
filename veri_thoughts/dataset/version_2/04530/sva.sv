module full_adder_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic cin,
    input logic cout,
    input logic sum
);

    // Sum matches the three-input XOR function.
    check_sum_function: assert property (
        @(posedge clk) sum == (a ^ b ^ cin)
    );

    // Carry-out matches the full-adder carry equation.
    check_cout_function: assert property (
        @(posedge clk) cout == ((a & b) | (a & cin) | (b & cin))
    );

    // All-zero inputs produce zero sum and zero carry.
    check_zero_case: assert property (
        @(posedge clk) (!a && !b && !cin) |-> (!sum && !cout)
    );

    // Any single high input produces sum high and no carry.
    check_single_one_case: assert property (
        @(posedge clk)
        ((a && !b && !cin) || (!a && b && !cin) || (!a && !b && cin))
        |-> (sum && !cout)
    );

    // Any two high inputs produce sum low and carry high.
    check_two_one_case: assert property (
        @(posedge clk)
        ((a && b && !cin) || (a && !b && cin) || (!a && b && cin))
        |-> (!sum && cout)
    );

    // All-one inputs produce sum high and carry high.
    check_all_one_case: assert property (
        @(posedge clk) (a && b && cin) |-> (sum && cout)
    );

    // Carry-out only occurs when at least two inputs are high.
    check_carry_requires_two_ones: assert property (
        @(posedge clk) cout |-> ((a && b) || (a && cin) || (b && cin))
    );

    // No carry occurs when fewer than two inputs are high.
    check_no_carry_with_fewer_than_two_ones: assert property (
        @(posedge clk) ((!a && !b) || (!a && !cin) || (!b && !cin)) |-> !cout
    );

    // Sum is high for odd input parity.
    check_sum_odd_parity: assert property (
        @(posedge clk)
        ((!a && !b && cin) || (!a && b && !cin) || (a && !b && !cin) || (a && b && cin))
        |-> sum
    );

    // Sum is low for even input parity.
    check_sum_even_parity: assert property (
        @(posedge clk)
        ((!a && !b && !cin) || (!a && b && cin) || (a && !b && cin) || (a && b && !cin))
        |-> !sum
    );

endmodule