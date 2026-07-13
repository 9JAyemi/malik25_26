module mux_2_1_sva (
    input logic clk,   // external sampling clock (RTL has no clock/reset)
    input logic a,
    input logic b,
    input logic sel,
    input logic out
);
    // out implements exact ternary function of inputs
    check_function_exact: assert property (
        @(posedge clk) out == ((sel == 1'b0) ? a : b)
    );

    // When sel==0, out equals a in the same cycle
    check_sel0_path: assert property (
        @(posedge clk) (sel == 1'b0) |-> (out == a)
    );

    // When sel==1, out equals b in the same cycle
    check_sel1_path: assert property (
        @(posedge clk) (sel == 1'b1) |-> (out == b)
    );

    // If out changes, at least one driver (a,b,sel) changed
    check_out_change_implies_driver_change: assert property (
        @(posedge clk) $changed(out) |-> ($changed(a) || $changed(b) || $changed(sel))
    );

    // If inputs and sel are stable, out must be stable
    check_stable_inputs_keep_out_stable: assert property (
        @(posedge clk) (!$changed(a) && !$changed(b) && !$changed(sel)) |-> !$changed(out)
    );

    // If sel toggles while a and b are stable and equal, out does not change
    check_sel_toggle_equal_inputs_no_out_change: assert property (
        @(posedge clk) $changed(sel) && !$changed(a) && !$changed(b) && (a === b) |-> !$changed(out)
    );

    // If sel toggles while a and b are stable and unequal, out changes
    check_sel_toggle_unequal_inputs_out_changes: assert property (
        @(posedge clk) $changed(sel) && !$changed(a) && !$changed(b) && (a !== b) |-> $changed(out)
    );

    // If sel==0 and only b changes, out does not change
    check_unselected_b_change_no_out_change: assert property (
        @(posedge clk) (sel == 1'b0) && !$changed(sel) && !$changed(a) && $changed(b) |-> !$changed(out)
    );

    // If sel==1 and only a changes, out does not change
    check_unselected_a_change_no_out_change: assert property (
        @(posedge clk) (sel == 1'b1) && !$changed(sel) && !$changed(b) && $changed(a) |-> !$changed(out)
    );

    // If sel==0 and only a changes, out changes
    check_selected_a_change_updates_out: assert property (
        @(posedge clk) (sel == 1'b0) && !$changed(sel) && $changed(a) && !$changed(b) |-> $changed(out)
    );

    // If sel==1 and only b changes, out changes
    check_selected_b_change_updates_out: assert property (
        @(posedge clk) (sel == 1'b1) && !$changed(sel) && $changed(b) && !$changed(a) |-> $changed(out)
    );
endmodule