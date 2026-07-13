module MUX2to1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic out
);

    ///// MUX functional correctness /////
    // Out equals selected input by sel.
    check_mux_function: assert property (
        @(posedge clk) out == (sel ? b : a)
    );

    // When sel is 0, out equals a.
    check_sel0_routes_a: assert property (
        @(posedge clk) (sel == 1'b0) |-> (out == a)
    );

    // When sel is 1, out equals b.
    check_sel1_routes_b: assert property (
        @(posedge clk) (sel == 1'b1) |-> (out == b)
    );

    ///// Change propagation and independence /////
    // A change on out implies sel changed or the currently selected input changed.
    check_out_change_cause: assert property (
        @(posedge clk) $changed(out) |-> ($changed(sel) || ((sel == 1'b1) && $changed(b)) || ((sel == 1'b0) && $changed(a)))
    );

    // When sel=0 and a,sel are stable, changes on b do not affect out.
    check_ignore_b_when_sel0: assert property (
        @(posedge clk) (sel == 1'b0) && $stable(sel) && $stable(a) && $changed(b) |-> $stable(out)
    );

    // When sel=1 and b,sel are stable, changes on a do not affect out.
    check_ignore_a_when_sel1: assert property (
        @(posedge clk) (sel == 1'b1) && $stable(sel) && $stable(b) && $changed(a) |-> $stable(out)
    );

    // When sel=0 and a changes (sel stable), out changes accordingly.
    check_selected_a_change_propagates: assert property (
        @(posedge clk) (sel == 1'b0) && $stable(sel) && $changed(a) |-> $changed(out)
    );

    // When sel=1 and b changes (sel stable), out changes accordingly.
    check_selected_b_change_propagates: assert property (
        @(posedge clk) (sel == 1'b1) && $stable(sel) && $changed(b) |-> $changed(out)
    );

endmodule