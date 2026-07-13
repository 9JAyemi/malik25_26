module min_finder_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [7:0] d,
    input logic [7:0] min
);

    // The output must match the RTL's full nested minimum expression.
    check_min_full_function: assert property (
        @(posedge clk)
        min == (
            (((a < b) ? a : b) < ((c < d) ? c : d)) ?
            ((a < b) ? a : b) :
            ((c < d) ? c : d)
        )
    );

    // The reported minimum cannot be greater than a.
    check_min_le_a: assert property (
        @(posedge clk)
        min <= a
    );

    // The reported minimum cannot be greater than b.
    check_min_le_b: assert property (
        @(posedge clk)
        min <= b
    );

    // The reported minimum cannot be greater than c.
    check_min_le_c: assert property (
        @(posedge clk)
        min <= c
    );

    // The reported minimum cannot be greater than d.
    check_min_le_d: assert property (
        @(posedge clk)
        min <= d
    );

    // The minimum value must match at least one input value.
    check_min_matches_input: assert property (
        @(posedge clk)
        (min == a) || (min == b) || (min == c) || (min == d)
    );

    // If a is no greater than the other inputs, min must equal a.
    check_a_when_a_is_smallest: assert property (
        @(posedge clk)
        ((a <= b) && (a <= c) && (a <= d)) |-> (min == a)
    );

    // If b is no greater than the other inputs, min must equal b.
    check_b_when_b_is_smallest: assert property (
        @(posedge clk)
        ((b <= a) && (b <= c) && (b <= d)) |-> (min == b)
    );

    // If c is no greater than the other inputs, min must equal c.
    check_c_when_c_is_smallest: assert property (
        @(posedge clk)
        ((c <= a) && (c <= b) && (c <= d)) |-> (min == c)
    );

    // If d is no greater than the other inputs, min must equal d.
    check_d_when_d_is_smallest: assert property (
        @(posedge clk)
        ((d <= a) && (d <= b) && (d <= c)) |-> (min == d)
    );

endmodule