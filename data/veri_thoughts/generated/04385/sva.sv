module multiplexer_sva (
    input logic sel,
    input logic in1,
    input logic in2,
    input logic out
);

    // Output must follow the exact RTL equation.
    check_out_matches_rtl_equation: assert property (
        @($global_clock) out == ((~sel & in1) | (sel & 1'b1))
    );

    // With sel low, out must pass in1.
    check_sel_low_passes_in1: assert property (
        @($global_clock) (sel == 1'b0) |-> (out == in1)
    );

    // With sel high, out must be forced high.
    check_sel_high_forces_out_high: assert property (
        @($global_clock) (sel == 1'b1) |-> (out == 1'b1)
    );

    // A low output requires both sel and in1 to be low.
    check_out_low_requires_sel_low_and_in1_low: assert property (
        @($global_clock) (out == 1'b0) |-> ((sel == 1'b0) && (in1 == 1'b0))
    );

    // Changing only in2 must not affect out.
    check_in2_unused: assert property (
        @($global_clock)
        (!$initstate && $changed(in2) && $stable(sel) && $stable(in1)) |-> $stable(out)
    );

    // Changing in1 while sel stays high must not affect out.
    check_in1_ignored_when_sel_high: assert property (
        @($global_clock)
        (!$initstate && (sel == 1'b1) && $stable(sel) && $changed(in1)) |-> $stable(out)
    );

    // Changing in1 while sel stays low must be reflected on out.
    check_in1_controls_out_when_sel_low: assert property (
        @($global_clock)
        (!$initstate && (sel == 1'b0) && $stable(sel) && $changed(in1)) |-> (out == in1)
    );

endmodule