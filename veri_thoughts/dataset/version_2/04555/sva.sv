module mux_2to1_sva (
    input logic in0,
    input logic in1,
    input logic sel,
    input logic out
);

    // No RTL clock or reset; sample this combinational mux on the formal global clock.
    // Output must always match the selected input.
    check_mux_function: assert property (
        @($global_clock) out === ((sel === 1'b0) ? in0 : in1)
    );

    // When select is exactly 0, out must route in0.
    check_sel_zero_routes_in0: assert property (
        @($global_clock) (sel === 1'b0) |-> (out === in0)
    );

    // When select is not exactly 0, out must route in1.
    check_sel_nonzero_routes_in1: assert property (
        @($global_clock) (sel !== 1'b0) |-> (out === in1)
    );

    // Changing the unselected in1 must not affect out when select is 0.
    check_in1_ignored_when_sel_zero: assert property (
        @($global_clock) (sel === 1'b0 && $stable(in0) && $changed(in1)) |-> $stable(out)
    );

    // Changing the unselected in0 must not affect out when select is not 0.
    check_in0_ignored_when_sel_nonzero: assert property (
        @($global_clock) (sel !== 1'b0 && $stable(in1) && $changed(in0)) |-> $stable(out)
    );

    // A select change to 0 must make out reflect in0 when inputs are stable.
    check_sel_change_to_zero_selects_in0: assert property (
        @($global_clock) ($changed(sel) && (sel === 1'b0) && $stable(in0) && $stable(in1)) |-> (out === in0)
    );

    // A select change away from 0 must make out reflect in1 when inputs are stable.
    check_sel_change_from_zero_selects_in1: assert property (
        @($global_clock) ($changed(sel) && (sel !== 1'b0) && $stable(in0) && $stable(in1)) |-> (out === in1)
    );

endmodule