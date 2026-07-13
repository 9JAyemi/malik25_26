module mux2to1_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic sel,
    input logic out
);
    // Output equals selected input every cycle.
    check_mux_function: assert property (
        @(posedge clk) disable iff (1'b0) out == (sel ? in2 : in1)
    );

    // When sel is 0, out equals in1.
    check_sel0_path: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 1'b0) |-> (out == in1)
    );

    // When sel is 1, out equals in2.
    check_sel1_path: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 1'b1) |-> (out == in2)
    );

    // Out is always equal to one of the inputs.
    check_out_is_one_of_inputs: assert property (
        @(posedge clk) disable iff (1'b0) ((out == in1) || (out == in2))
    );

    // Out changes only if sel or the selected input changes.
    check_out_change_causes: assert property (
        @(posedge clk) disable iff (1'b0) $changed(out) |-> ($changed(sel) || (sel ? $changed(in2) : $changed(in1)))
    );

    // If all inputs are stable, out remains stable.
    check_out_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0) ($stable(sel) && $stable(in1) && $stable(in2)) |-> $stable(out)
    );

    // If out differs from in1, sel must be 1.
    check_out_ne_in1_implies_sel1: assert property (
        @(posedge clk) disable iff (1'b0) (out != in1) |-> (sel == 1'b1)
    );

    // If out differs from in2, sel must be 0.
    check_out_ne_in2_implies_sel0: assert property (
        @(posedge clk) disable iff (1'b0) (out != in2) |-> (sel == 1'b0)
    );

    // With sel=0 and stable, an out change implies in1 changed.
    check_sel0_out_change_implies_in1_change: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 1'b0 && $stable(sel) && $changed(out)) |-> $changed(in1)
    );

    // With sel=1 and stable, an out change implies in2 changed.
    check_sel1_out_change_implies_in2_change: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 1'b1 && $stable(sel) && $changed(out)) |-> $changed(in2)
    );

    // If sel toggles and inputs are equal, out does not change.
    check_sel_toggle_equal_inputs_no_out_change: assert property (
        @(posedge clk) disable iff (1'b0) ($changed(sel) && $stable(in1) && $stable(in2) && (in1 == in2)) |-> !$changed(out)
    );

    // If sel toggles and inputs differ, out changes.
    check_sel_toggle_diff_inputs_out_change: assert property (
        @(posedge clk) disable iff (1'b0) ($changed(sel) && $stable(in1) && $stable(in2) && (in1 != in2)) |-> $changed(out)
    );
endmodule