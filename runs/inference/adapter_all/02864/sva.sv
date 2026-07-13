module mux2_sva (
    input logic clk,
    input logic sel,
    input logic in1,
    input logic in2,
    input logic out
);
    // Out equals the previous cycle's selected input.
    check_registered_mux_function: assert property (
        @(posedge clk) disable iff ($initstate) out == $past((sel == 1'b0) ? in1 : in2)
    );

    // When sel was 0 last cycle, out equals previous in1.
    check_sel0_path: assert property (
        @(posedge clk) disable iff ($initstate) ($past(sel) == 1'b0) |-> (out == $past(in1))
    );

    // When sel was 1 last cycle, out equals previous in2.
    check_sel1_path: assert property (
        @(posedge clk) disable iff ($initstate) ($past(sel) == 1'b1) |-> (out == $past(in2))
    );

    // If sel and both inputs were stable last cycle, out is stable this cycle.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) disable iff ($initstate) ($past(sel) == $past(sel,2) && $past(in1) == $past(in1,2) && $past(in2) == $past(in2,2)) |-> (out == $past(out))
    );

    // If sel was 0 last cycle and in1 changed, out changes this cycle.
    check_out_changes_when_sel0_in1_changes: assert property (
        @(posedge clk) disable iff ($initstate) ($past(sel) == 1'b0 && $past(in1) != $past(in1,2)) |-> (out != $past(out))
    );

    // If sel was 1 last cycle and in2 changed, out changes this cycle.
    check_out_changes_when_sel1_in2_changes: assert property (
        @(posedge clk) disable iff ($initstate) ($past(sel) == 1'b1 && $past(in2) != $past(in2,2)) |-> (out != $past(out))
    );

    // If sel was 0 last cycle and in1 was stable, out is stable this cycle.
    check_out_stable_when_sel0_in1_stable: assert property (
        @(posedge clk) disable iff ($initstate) ($past(sel) == 1'b0 && $past(in1) == $past(in1,2)) |-> (out == $past(out))
    );

    // If sel was 1 last cycle and in2 was stable, out is stable this cycle.
    check_out_stable_when_sel1_in2_stable: assert property (
        @(posedge clk) disable iff ($initstate) ($past(sel) == 1'b1 && $past(in2) == $past(in2,2)) |-> (out == $past(out))
    );

    // If sel toggled and both inputs were stable last cycle, out toggles this cycle.
    check_out_toggles_on_sel_toggle_when_inputs_stable: assert property (
        @(posedge clk) disable iff ($initstate) ($past(sel) != $past(sel,2) && $past(in1) == $past(in1,2) && $past(in2) == $past(in2,2)) |-> (out != $past(out))
    );

    // If sel toggled and both inputs were different last cycle, out does not toggle this cycle.
    check_out_stable_on_sel_toggle_when_inputs_differ: assert property (
        @(posedge clk) disable iff ($initstate) ($past(sel) != $past(sel,2) && $past(in1) != $past(in2)) |-> (out == $past(out))
    );
endmodule