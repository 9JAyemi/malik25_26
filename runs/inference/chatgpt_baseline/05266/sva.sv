module top_module_sva (
    input logic        clk,
    input logic [7:0]  a,
    input logic [7:0]  b,
    input logic [7:0]  c,
    input logic [7:0]  d,
    input logic [7:0]  max
);

    // max matches the nested comparator implementation.
    check_nested_compare_equivalence: assert property (
        @(posedge clk)
        max == ((((a > b) ? a : b) > ((c > d) ? c : d)) ? ((a > b) ? a : b) : ((c > d) ? c : d))
    );

    // max is never smaller than a.
    check_max_ge_a: assert property (
        @(posedge clk)
        max >= a
    );

    // max is never smaller than b.
    check_max_ge_b: assert property (
        @(posedge clk)
        max >= b
    );

    // max is never smaller than c.
    check_max_ge_c: assert property (
        @(posedge clk)
        max >= c
    );

    // max is never smaller than d.
    check_max_ge_d: assert property (
        @(posedge clk)
        max >= d
    );

    // max must equal one of the four inputs.
    check_max_matches_an_input: assert property (
        @(posedge clk)
        (max == a) || (max == b) || (max == c) || (max == d)
    );

    // If a is at least as large as all others, max equals a.
    check_a_is_max_value: assert property (
        @(posedge clk)
        ((a >= b) && (a >= c) && (a >= d)) |-> (max == a)
    );

    // If b is at least as large as all others, max equals b.
    check_b_is_max_value: assert property (
        @(posedge clk)
        ((b >= a) && (b >= c) && (b >= d)) |-> (max == b)
    );

    // If c is at least as large as all others, max equals c.
    check_c_is_max_value: assert property (
        @(posedge clk)
        ((c >= a) && (c >= b) && (c >= d)) |-> (max == c)
    );

    // If d is at least as large as all others, max equals d.
    check_d_is_max_value: assert property (
        @(posedge clk)
        ((d >= a) && (d >= b) && (d >= c)) |-> (max == d)
    );

endmodule