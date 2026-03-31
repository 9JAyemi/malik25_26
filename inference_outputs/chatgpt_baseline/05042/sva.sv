module top_module_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [7:0] d,
    input logic [7:0] min
);

    // RTL is combinational and has no native clock or reset; sample it on clk.

    // min must match the RTL's nested minimum calculation.
    check_min_matches_rtl_function: assert property (
        @(posedge clk)
        min == ((((a < b) ? a : b) < ((c < d) ? c : d)) ? ((a < b) ? a : b) : ((c < d) ? c : d))
    );

    // min must be less than or equal to every input.
    check_min_le_all_inputs: assert property (
        @(posedge clk)
        (min <= a) && (min <= b) && (min <= c) && (min <= d)
    );

    // min must equal one of the four inputs.
    check_min_matches_an_input: assert property (
        @(posedge clk)
        (min == a) || (min == b) || (min == c) || (min == d)
    );

    // If a is a minimum value, min must equal a.
    check_a_drives_min_when_lowest: assert property (
        @(posedge clk)
        (a <= b && a <= c && a <= d) |-> (min == a)
    );

    // If b is a minimum value, min must equal b.
    check_b_drives_min_when_lowest: assert property (
        @(posedge clk)
        (b <= a && b <= c && b <= d) |-> (min == b)
    );

    // If c is a minimum value, min must equal c.
    check_c_drives_min_when_lowest: assert property (
        @(posedge clk)
        (c <= a && c <= b && c <= d) |-> (min == c)
    );

    // If d is a minimum value, min must equal d.
    check_d_drives_min_when_lowest: assert property (
        @(posedge clk)
        (d <= a && d <= b && d <= c) |-> (min == d)
    );

endmodule