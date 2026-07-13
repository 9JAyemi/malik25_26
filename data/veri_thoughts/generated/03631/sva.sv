module mux_2to1_assertions (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic sel,
    input logic VPWR,
    input logic VGND
);

    // X must match the implemented bitwise mux equation.
    check_mux_equation: assert property (
        @(posedge clk) X === ((sel & B) | ((~sel) & A))
    );

    // With sel low and A known, X follows A.
    check_sel_low_selects_a: assert property (
        @(posedge clk) (sel === 1'b0 && !$isunknown(A)) |-> (X === A)
    );

    // With sel high and B known, X follows B.
    check_sel_high_selects_b: assert property (
        @(posedge clk) (sel === 1'b1 && !$isunknown(B)) |-> (X === B)
    );

    // With sel low and A unknown, X becomes unknown.
    check_sel_low_unknown_a_propagates: assert property (
        @(posedge clk) (sel === 1'b0 && $isunknown(A)) |-> $isunknown(X)
    );

    // With sel high and B unknown, X becomes unknown.
    check_sel_high_unknown_b_propagates: assert property (
        @(posedge clk) (sel === 1'b1 && $isunknown(B)) |-> $isunknown(X)
    );

    // If both data inputs are 0, X is forced low.
    check_both_zero_force_zero: assert property (
        @(posedge clk) (A === 1'b0 && B === 1'b0) |-> (X === 1'b0)
    );

    // If A, B, and sel are stable, X stays stable.
    check_x_stable_when_function_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(sel)) |-> $stable(X)
    );

    // B is ignored while sel stays low and A stays stable.
    check_b_ignored_when_sel_low: assert property (
        @(posedge clk) (sel === 1'b0 && $stable(sel) && $stable(A)) |-> $stable(X)
    );

    // A is ignored while sel stays high and B stays stable.
    check_a_ignored_when_sel_high: assert property (
        @(posedge clk) (sel === 1'b1 && $stable(sel) && $stable(B)) |-> $stable(X)
    );

    // VPWR and VGND do not affect X when functional inputs are stable.
    check_power_pins_ignored: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(sel) &&
                        ($changed(VPWR) || $changed(VGND))) |-> $stable(X)
    );

endmodule