module mux_2to1_controlled_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic sel_a,
    input logic sel_b1,
    input logic sel_b2,
    input logic out_mux
);

    // sel_a has highest priority and selects a.
    check_sel_a_priority: assert property (
        @(posedge clk) sel_a |-> (out_mux == a)
    );

    // When sel_a is low and both sel_b controls are low, b is selected.
    check_select_b_when_sel_b_low: assert property (
        @(posedge clk) (!sel_a && !sel_b1 && !sel_b2) |-> (out_mux == b)
    );

    // When sel_a is low and both sel_b controls are high, c is selected.
    check_select_c_when_sel_b_high: assert property (
        @(posedge clk) (!sel_a && sel_b1 && sel_b2) |-> (out_mux == c)
    );

    // When sel_a is low and the sel_b controls differ, d is selected.
    check_select_d_when_sel_b_mixed: assert property (
        @(posedge clk) (!sel_a && ((sel_b1 && !sel_b2) || (!sel_b1 && sel_b2))) |-> (out_mux == d)
    );

endmodule