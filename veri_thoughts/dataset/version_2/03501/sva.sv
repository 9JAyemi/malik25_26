module full_adder_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic cin,
    input logic sum,
    input logic cout
);

    // sum is the XOR of a, b, and cin.
    check_sum_function: assert property (
        @(posedge clk) sum == (a ^ b ^ cin)
    );

    // cout is high when at least two inputs are high.
    check_cout_function: assert property (
        @(posedge clk) cout == ((a & b) | (a & cin) | (b & cin))
    );

    // All-zero inputs produce zero sum and zero carry.
    check_all_zero_case: assert property (
        @(posedge clk) (!a && !b && !cin) |-> (!sum && !cout)
    );

    // All-one inputs produce zero sum and asserted carry.
    check_all_one_case: assert property (
        @(posedge clk) (a && b && cin) |-> (!sum && cout)
    );

    // Exactly one high input produces sum high and carry low.
    check_single_high_case: assert property (
        @(posedge clk)
        ((a && !b && !cin) || (!a && b && !cin) || (!a && !b && cin))
        |-> (sum && !cout)
    );

    // Exactly two high inputs produce sum low and carry high.
    check_two_high_case: assert property (
        @(posedge clk)
        ((a && b && !cin) || (a && !b && cin) || (!a && b && cin))
        |-> (!sum && cout)
    );

endmodule