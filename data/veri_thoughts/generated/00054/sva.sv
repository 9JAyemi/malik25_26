module mux_2to1_sva (
    input logic in0,
    input logic in1,
    input logic sel,
    input logic out
);

    // No RTL clock or reset; sample the combinational behavior on $global_clock.

    // When select is low, out must equal in0.
    check_sel_low_routes_in0: assert property (
        @($global_clock) (sel == 1'b0) |-> (out == in0)
    );

    // When select is high, out must equal in1.
    check_sel_high_routes_in1: assert property (
        @($global_clock) (sel == 1'b1) |-> (out == in1)
    );

    // A selected in0 change must be reflected at out.
    check_in0_change_updates_out_when_sel_low: assert property (
        @($global_clock)
        (!$initstate && ($past(sel) == 1'b0) && (sel == 1'b0) && $changed(in0)) |-> $changed(out)
    );

    // A selected in1 change must be reflected at out.
    check_in1_change_updates_out_when_sel_high: assert property (
        @($global_clock)
        (!$initstate && ($past(sel) == 1'b1) && (sel == 1'b1) && $changed(in1)) |-> $changed(out)
    );

    // An in1 change cannot affect out while sel stays low and in0 is stable.
    check_in1_change_ignored_when_sel_low: assert property (
        @($global_clock)
        (!$initstate && ($past(sel) == 1'b0) && (sel == 1'b0) && $stable(in0) && $changed(in1)) |-> $stable(out)
    );

    // An in0 change cannot affect out while sel stays high and in1 is stable.
    check_in0_change_ignored_when_sel_high: assert property (
        @($global_clock)
        (!$initstate && ($past(sel) == 1'b1) && (sel == 1'b1) && $stable(in1) && $changed(in0)) |-> $stable(out)
    );

    // A select change must toggle out when inputs are different and stable.
    check_sel_change_toggles_out_when_inputs_differ: assert property (
        @($global_clock)
        (!$initstate && $changed(sel) && $stable(in0) && $stable(in1) && (in0 != in1)) |-> $changed(out)
    );

    // A select change must not change out when inputs match and are stable.
    check_sel_change_holds_out_when_inputs_match: assert property (
        @($global_clock)
        (!$initstate && $changed(sel) && $stable(in0) && $stable(in1) && (in0 == in1)) |-> $stable(out)
    );

endmodule