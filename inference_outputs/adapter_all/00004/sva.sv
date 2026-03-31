module mux_2to1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic y
);

    // y must match the implemented 2:1 mux equation.
    check_mux_equation: assert property (
        @(posedge clk) y == ((~sel & a) | (sel & b))
    );

    // When sel is low, y must follow a.
    check_sel_low_routes_a: assert property (
        @(posedge clk) !sel |-> (y == a)
    );

    // When sel is high, y must follow b.
    check_sel_high_routes_b: assert property (
        @(posedge clk) sel |-> (y == b)
    );

    // With sel low and a stable, y must remain stable.
    check_sel_low_stable_a_keeps_y_stable: assert property (
        @(posedge clk) (!sel && $stable(sel) && $stable(a)) |-> $stable(y)
    );

    // With sel high and b stable, y must remain stable.
    check_sel_high_stable_b_keeps_y_stable: assert property (
        @(posedge clk) (sel && $stable(sel) && $stable(b)) |-> $stable(y)
    );

    // With sel low and a changing, y must change.
    check_sel_low_a_change_changes_y: assert property (
        @(posedge clk) (!sel && $stable(sel) && $changed(a)) |-> $changed(y)
    );

    // With sel high and b changing, y must change.
    check_sel_high_b_change_changes_y: assert property (
        @(posedge clk) (sel && $stable(sel) && $changed(b)) |-> $changed(y)
    );

    // With sel low and a stable, a change on b must not affect y.
    check_sel_low_b_change_ignored: assert property (
        @(posedge clk) (!sel && $stable(sel) && $stable(a) && $changed(b)) |-> $stable(y)
    );

    // With sel high and b stable, a change on a must not affect y.
    check_sel_high_a_change_ignored: assert property (
        @(posedge clk) (sel && $stable(sel) && $stable(b) && $changed(a)) |-> $stable(y)
    );

endmodule