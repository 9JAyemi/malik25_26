module mux_2_to_1_sva (
    input logic CLK,
    input logic a,
    input logic b,
    input logic sel,
    input logic out
);
    // Output equals selected input functionally every cycle.
    check_mux_function_equivalence: assert property (
        @(posedge CLK) out == (sel ? b : a)
    );

    // When sel=0, out mirrors a.
    check_route_when_sel0: assert property (
        @(posedge CLK) (sel == 1'b0) |-> (out == a)
    );

    // When sel=1, out mirrors b.
    check_route_when_sel1: assert property (
        @(posedge CLK) (sel == 1'b1) |-> (out == b)
    );

    // Out can only change if a, b, or sel changed.
    check_out_changes_only_with_inputs: assert property (
        @(posedge CLK) $changed(out) |-> $changed({a,b,sel})
    );

    // If a, b, and sel are stable, out is stable.
    check_out_stable_if_inputs_stable: assert property (
        @(posedge CLK) $stable({a,b,sel}) |-> $stable(out)
    );

    // On sel rising edge, out equals b immediately.
    check_sel_rise_routes_b_now: assert property (
        @(posedge CLK) $rose(sel) |-> (out == b)
    );

    // On sel falling edge, out equals a immediately.
    check_sel_fall_routes_a_now: assert property (
        @(posedge CLK) $fell(sel) |-> (out == a)
    );

    // If sel stays 0 and a changes, out changes.
    check_selected_a_change_updates_out: assert property (
        @(posedge CLK) (sel == 1'b0 && $stable(sel) && $changed(a)) |-> $changed(out)
    );

    // If sel stays 1 and b changes, out changes.
    check_selected_b_change_updates_out: assert property (
        @(posedge CLK) (sel == 1'b1 && $stable(sel) && $changed(b)) |-> $changed(out)
    );
endmodule