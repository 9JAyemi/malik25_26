module top_module_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [7:0] d,
    input logic [7:0] min
);

    // min must match the RTL's nested minimum selection.
    check_min_matches_rtl: assert property (
        @($global_clock)
        min == ((a < b) ? a : b) <= ((c < d) ? c : d)
    );

    // min must be less than or equal to a.
    check_min_le_a: assert property (
        @($global_clock)
        min <= a
    );

    // min must be less than or equal to b.
    check_min_le_b: assert property (
        @($global_clock)
        min <= b
    );

    // min must be less than or equal to c.
    check_min_le_c: assert property (
        @($global_clock)
        min <= c
    );

    // min must be less than or equal to d.
    check_min_le_d: assert property (
        @($global_clock)
        min <= d
    );

    // If a is less than or equal to b, min must equal a.
    check_a_selected_when_a_le_b: assert property (
        @($global_clock)
        (a <= b) |-> (min == a)
    );

    // If a is greater than b, min must equal b.
    check_b_selected_when_a_gt_b: assert property (
        @($global_clock)
        (a > b) |-> (min == b)
    );

    // If c is less than or equal to d, min must equal c.
    check_c_selected_when_c_le_d: assert property (
        @($global_clock)
        (c <= d) |-> (min == c)
    );

    // If c is greater than d, min must equal d.
    check_d_selected_when_c_gt_d: assert property (
        @($global_clock)
        (c > d) |-> (min == d)
    );

endmodule