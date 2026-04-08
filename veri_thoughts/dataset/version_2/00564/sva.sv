module four_way_min_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [7:0] d,
    input logic [7:0] min
);

    logic [7:0] ab_min, cd_min, abcd_min;

    assign ab_min   = (a < b) ? a : b;
    assign cd_min   = (c < d) ? c : d;
    assign abcd_min = (ab_min < cd_min) ? ab_min : cd_min;

    // Output must match the RTL minimum computation.
    check_output_matches_rtl: assert property (
        @(posedge clk) min == abcd_min
    );

    // The reported minimum cannot exceed input a.
    check_min_le_a: assert property (
        @(posedge clk) min <= a
    );

    // The reported minimum cannot exceed input b.
    check_min_le_b: assert property (
        @(posedge clk) min <= b
    );

    // The reported minimum cannot exceed input c.
    check_min_le_c: assert property (
        @(posedge clk) min <= c
    );

    // The reported minimum cannot exceed input d.
    check_min_le_d: assert property (
        @(posedge clk) min <= d
    );

    // The reported minimum must be one of the four inputs.
    check_min_is_input_value: assert property (
        @(posedge clk) (min == a) || (min == b) || (min == c) || (min == d)
    );

    // If a is no greater than all other inputs, the output must equal a.
    check_a_when_a_is_minimal: assert property (
        @(posedge clk) ((a <= b) && (a <= c) && (a <= d)) |-> (min == a)
    );

    // If b is no greater than all other inputs, the output must equal b.
    check_b_when_b_is_minimal: assert property (
        @(posedge clk) ((b <= a) && (b <= c) && (b <= d)) |-> (min == b)
    );

    // If c is no greater than all other inputs, the output must equal c.
    check_c_when_c_is_minimal: assert property (
        @(posedge clk) ((c <= a) && (c <= b) && (c <= d)) |-> (min == c)
    );

    // If d is no greater than all other inputs, the output must equal d.
    check_d_when_d_is_minimal: assert property (
        @(posedge clk) ((d <= a) && (d <= b) && (d <= c)) |-> (min == d)
    );

endmodule