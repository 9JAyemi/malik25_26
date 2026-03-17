module sky130_fd_sc_ms__mux_2_1_sva (
    input logic out,
    input logic in0,
    input logic in1,
    input logic sel,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Out always equals the selected data input.
    check_mux_equation: assert property (
        @($global_clock) out == (sel ? in1 : in0)
    );

    // When sel is low, out matches in0.
    check_sel_low_selects_in0: assert property (
        @($global_clock) !sel |-> (out == in0)
    );

    // When sel is high, out matches in1.
    check_sel_high_selects_in1: assert property (
        @($global_clock) sel |-> (out == in1)
    );

    // A change on in0 is reflected when in0 is selected.
    check_in0_change_reflected_when_selected: assert property (
        @($global_clock) $stable(sel) && !sel && $changed(in0) |-> (out == in0)
    );

    // A change on in1 is reflected when in1 is selected.
    check_in1_change_reflected_when_selected: assert property (
        @($global_clock) $stable(sel) && sel && $changed(in1) |-> (out == in1)
    );

    // A change on in0 is ignored when in1 remains selected.
    check_in0_change_ignored_when_unselected: assert property (
        @($global_clock) $stable(sel) && sel && $stable(in1) && $changed(in0) |-> $stable(out)
    );

    // A change on in1 is ignored when in0 remains selected.
    check_in1_change_ignored_when_unselected: assert property (
        @($global_clock) $stable(sel) && !sel && $stable(in0) && $changed(in1) |-> $stable(out)
    );

    // A rising sel switches the output to in1 when data inputs are stable.
    check_sel_rise_selects_in1: assert property (
        @($global_clock) $rose(sel) && $stable(in0) && $stable(in1) |-> (out == in1)
    );

    // A falling sel switches the output to in0 when data inputs are stable.
    check_sel_fall_selects_in0: assert property (
        @($global_clock) $fell(sel) && $stable(in0) && $stable(in1) |-> (out == in0)
    );

    // Stable functional inputs keep the output stable.
    check_stable_inputs_keep_output_stable: assert property (
        @($global_clock) $stable(sel) && $stable(in0) && $stable(in1) |-> $stable(out)
    );

endmodule