module mux_sva (
    // Note: RTL has no clock/reset; use CLK only for sampling assertions.
    input logic CLK,
    input logic in0,
    input logic in1,
    input logic sel,
    input logic out
);
    // out equals selected input per mux function.
    check_mux_equivalence: assert property (
        @(posedge CLK) out == (sel ? in1 : in0)
    );

    // When sel is 0, out mirrors in0.
    check_sel0_path: assert property (
        @(posedge CLK) (sel == 1'b0) |-> (out == in0)
    );

    // When sel is 1, out mirrors in1.
    check_sel1_path: assert property (
        @(posedge CLK) (sel == 1'b1) |-> (out == in1)
    );

    // On a rising edge of sel, out equals in1 in the same cycle.
    check_sel_rise_selects_in1: assert property (
        @(posedge CLK) $rose(sel) |-> (out == in1)
    );

    // On a falling edge of sel, out equals in0 in the same cycle.
    check_sel_fall_selects_in0: assert property (
        @(posedge CLK) $fell(sel) |-> (out == in0)
    );

    // If inputs are equal, out equals that common value regardless of sel.
    check_inputs_equal_forces_out: assert property (
        @(posedge CLK) (in0 == in1) |-> (out == in0)
    );

    // If sel and both inputs are stable, out must be stable.
    check_no_spurious_change: assert property (
        @(posedge CLK) $stable(sel) && $stable(in0) && $stable(in1) |-> $stable(out)
    );

    // Out can change only if at least one of sel/in0/in1 changes.
    check_out_change_has_cause: assert property (
        @(posedge CLK) $changed(out) |-> ($changed(sel) || $changed(in0) || $changed(in1))
    );
endmodule