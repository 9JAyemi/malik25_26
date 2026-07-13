module top_module_sva(
    input logic clk,
    input logic a,
    input logic b,
    input logic [255:0] in,
    input logic [2:0] sel,
    input logic out_func
);

    // out_func always equals the XNOR of a and b.
    check_out_func_matches_xnor: assert property (
        @(posedge clk) disable iff (1'b0)
        out_func == (a ~^ b)
    );

    // Equal input bits drive the output high.
    check_equal_inputs_drive_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (a == b) |-> (out_func == 1'b1)
    );

    // Different input bits drive the output low.
    check_different_inputs_drive_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (a != b) |-> (out_func == 1'b0)
    );

    // Holding a and b stable keeps the output stable.
    check_stable_ab_keep_output_stable: assert property (
        @(posedge clk) disable iff (1'b0)
        !$initstate && (a == $past(a)) && (b == $past(b)) |-> (out_func == $past(out_func))
    );

    // Changing sel alone does not affect the output.
    check_sel_change_does_not_affect_output: assert property (
        @(posedge clk) disable iff (1'b0)
        !$initstate && (a == $past(a)) && (b == $past(b)) &&
        (in == $past(in)) && (sel != $past(sel)) |-> (out_func == $past(out_func))
    );

    // Changing the input bus alone does not affect the output.
    check_in_change_does_not_affect_output: assert property (
        @(posedge clk) disable iff (1'b0)
        !$initstate && (a == $past(a)) && (b == $past(b)) &&
        (sel == $past(sel)) && (in != $past(in)) |-> (out_func == $past(out_func))
    );

    // Toggling a alone flips the output.
    check_a_toggle_flips_output: assert property (
        @(posedge clk) disable iff (1'b0)
        !$initstate && $changed(a) && (b == $past(b)) |-> (out_func != $past(out_func))
    );

    // Toggling b alone flips the output.
    check_b_toggle_flips_output: assert property (
        @(posedge clk) disable iff (1'b0)
        !$initstate && $changed(b) && (a == $past(a)) |-> (out_func != $past(out_func))
    );

    // Toggling a and b together keeps the output unchanged.
    check_ab_toggle_together_keep_output: assert property (
        @(posedge clk) disable iff (1'b0)
        !$initstate && $changed(a) && $changed(b) |-> (out_func == $past(out_func))
    );

endmodule