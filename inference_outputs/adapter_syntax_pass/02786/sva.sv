module mux_2_1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic out
);

    // When sel is low, out must equal a.
    check_sel_low_routes_a: assert property (
        @(posedge clk) (sel == 1'b0) |-> (out == a)
    );

    // When sel is high, out must equal b.
    check_sel_high_routes_b: assert property (
        @(posedge clk) (sel == 1'b1) |-> (out == b)
    );

    // With sel low and a stable, out must remain stable.
    check_stable_when_sel_low_and_a_stable: assert property (
        @(posedge clk) ((sel == 1'b0) && $stable(sel) && $stable(a)) |-> $stable(out)
    );

    // With sel high and b stable, out must remain stable.
    check_stable_when_sel_high_and_b_stable: assert property (
        @(posedge clk) ((sel == 1'b1) && $stable(sel) && $stable(b)) |-> $stable(out)
    );

    // With sel low and a changing, out must change.
    check_change_propagation_when_sel_low_and_a_changes: assert property (
        @(posedge clk) ((sel == 1'b0) && $stable(sel) && $changed(a)) |-> $changed(out)
    );

    // With sel high and b changing, out must change.
    check_change_propagation_when_sel_high_and_b_changes: assert property (
        @(posedge clk) ((sel == 1'b1) && $stable(sel) && $changed(b)) |-> $changed(out)
    );

endmodule