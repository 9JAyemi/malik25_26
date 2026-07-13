module mux_4to1_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic enable,
    input logic [3:0] out
);

    // When disabled, the output is forced low.
    check_disabled_forces_zero: assert property (
        @($global_clock) !enable |-> (out == 4'b0000)
    );

    // When enabled and sel is 00, out follows in0.
    check_sel_00_routes_in0: assert property (
        @($global_clock) (enable && (sel == 2'b00)) |-> (out == in0)
    );

    // When enabled and sel is 01, out follows in1.
    check_sel_01_routes_in1: assert property (
        @($global_clock) (enable && (sel == 2'b01)) |-> (out == in1)
    );

    // When enabled and sel is 10, out follows in2.
    check_sel_10_routes_in2: assert property (
        @($global_clock) (enable && (sel == 2'b10)) |-> (out == in2)
    );

    // When enabled and sel is 11, out follows in3.
    check_sel_11_routes_in3: assert property (
        @($global_clock) (enable && (sel == 2'b11)) |-> (out == in3)
    );

    // With enable high and sel stable, out stays stable.
    check_stable_when_enabled_and_sel_stable: assert property (
        @($global_clock) (enable && $stable(sel)) |-> $stable(out)
    );

    // With enable high and sel changing, out still follows the selected input.
    check_selected_input_change_updates_out: assert property (
        @($global_clock)
        (enable &&
         $changed(sel) &&
         ((sel == 2'b00) || (sel == 2'b01) || (sel == 2'b10) || (sel == 2'b11)))
        |-> (out == ($past(sel) == 2'b00 ? $past(in0) :
                     $past(sel) == 2'b01 ? $past(in1) :
                     $past(sel) == 2'b10 ? $past(in2) :
                                           $past(in3)))
    );

endmodule