module full_adder_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic cin,
    input logic s,
    input logic cout
);

    // Sum must match the XOR of the three inputs.
    check_sum_function: assert property (
        @(posedge clk) s == (a ^ b ^ cin)
    );

    // Carry-out must match the implemented carry equation.
    check_carry_function: assert property (
        @(posedge clk) cout == ((a & b) | (cin & (a ^ b)))
    );

    // All-zero inputs must produce zero sum and zero carry.
    check_zero_case: assert property (
        @(posedge clk) (!a && !b && !cin) |-> (!s && !cout)
    );

    // Exactly one high input must produce sum high and carry low.
    check_one_hot_case: assert property (
        @(posedge clk)
        ((a && !b && !cin) || (!a && b && !cin) || (!a && !b && cin))
        |-> (s && !cout)
    );

    // Exactly two high inputs must produce sum low and carry high.
    check_two_hot_case: assert property (
        @(posedge clk)
        ((a && b && !cin) || (a && !b && cin) || (!a && b && cin))
        |-> (!s && cout)
    );

    // All-high inputs must produce sum high and carry high.
    check_all_high_case: assert property (
        @(posedge clk) (a && b && cin) |-> (s && cout)
    );

endmodule