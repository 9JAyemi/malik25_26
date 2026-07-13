module mux_2to1_sva (
    input logic sel,
    input logic in0,
    input logic in1,
    input logic out
);
    // When sel is 0, out equals in0.
    check_out_when_sel0: assert property (
        @(posedge sel or negedge sel or posedge in0 or negedge in0 or posedge in1 or negedge in1)
        (sel == 1'b0) |-> (out == in0)
    );

    // When sel is 1, out equals in1.
    check_out_when_sel1: assert property (
        @(posedge sel or negedge sel or posedge in0 or negedge in0 or posedge in1 or negedge in1)
        (sel == 1'b1) |-> (out == in1)
    );

    // Out implements the mux equation at each input edge.
    check_mux_equation: assert property (
        @(posedge sel or negedge sel or posedge in0 or negedge in0 or posedge in1 or negedge in1)
        (out == (sel ? in1 : in0))
    );

    // If data inputs are equal, out equals that value.
    check_equal_inputs_reflect: assert property (
        @(posedge sel or negedge sel or posedge in0 or negedge in0 or posedge in1 or negedge in1)
        (in0 == in1) |-> (out == in0)
    );

    // Out only changes when at least one of sel/in0/in1 changes.
    check_out_only_changes_with_inputs: assert property (
        @(posedge sel or negedge sel or posedge in0 or negedge in0 or posedge in1 or negedge in1)
        $changed(out) |-> ($changed(sel) || $changed(in0) || $changed(in1))
    );

    // With sel stable at 1, out follows in1 changes.
    check_out_follows_in1_when_sel1_stable: assert property (
        @(posedge sel or negedge sel or posedge in0 or negedge in0 or posedge in1 or negedge in1)
        (sel && $stable(sel) && $changed(in1)) |-> $changed(out)
    );

    // With sel stable at 0, out follows in0 changes.
    check_out_follows_in0_when_sel0_stable: assert property (
        @(posedge sel or negedge sel or posedge in0 or negedge in0 or posedge in1 or negedge in1)
        (!sel && $stable(sel) && $changed(in0)) |-> $changed(out)
    );

    // With sel stable at 1, changes on in0 alone do not change out.
    check_ignore_in0_when_sel1_only_in0_changes: assert property (
        @(posedge sel or negedge sel or posedge in0 or negedge in0 or posedge in1 or negedge in1)
        (sel && $stable(sel) && $changed(in0) && !$changed(in1)) |-> !$changed(out)
    );

    // With sel stable at 0, changes on in1 alone do not change out.
    check_ignore_in1_when_sel0_only_in1_changes: assert property (
        @(posedge sel or negedge sel or posedge in0 or negedge in0 or posedge in1 or negedge in1)
        (!sel && $stable(sel) && $changed(in1) && !$changed(in0)) |-> !$changed(out)
    );

    // When sel toggles and inputs differ and are stable, out toggles.
    check_out_changes_on_sel_toggle_when_inputs_differ: assert property (
        @(posedge sel or negedge sel or posedge in0 or negedge in0 or posedge in1 or negedge in1)
        ($changed(sel) && $stable(in0) && $stable(in1) && (in0 != in1)) |-> $changed(out)
    );

    // When sel toggles and inputs are equal and stable, out stays the same.
    check_out_stable_on_sel_toggle_when_inputs_equal: assert property (
        @(posedge sel or negedge sel or posedge in0 or negedge in0 or posedge in1 or negedge in1)
        ($changed(sel) && $stable(in0) && $stable(in1) && (in0 == in1)) |-> !$changed(out)
    );

    // If sel is stable, any out change is explained by the selected data input.
    check_out_change_explained_by_selected_input: assert property (
        @(posedge sel or negedge sel or posedge in0 or negedge in0 or posedge in1 or negedge in1)
        ($changed(out) && $stable(sel)) |-> ((sel && $changed(in1)) || (!sel && $changed(in0)))
    );
endmodule