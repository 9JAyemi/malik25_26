module mux4_to_1_async_reset_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic reset,
    input logic [3:0] out
);

    // Reset forces the output to zero.
    check_reset_forces_zero: assert property (
        @($global_clock) reset |-> (out == 4'b0000)
    );

    // Select 00 routes in0 when reset is low.
    check_sel_00_routes_in0: assert property (
        @($global_clock) disable iff (reset)
        (sel == 2'b00) |-> (out == in0)
    );

    // Select 01 routes in0 when reset is low.
    check_sel_01_routes_in0: assert property (
        @($global_clock) disable iff (reset)
        (sel == 2'b01) |-> (out == in0)
    );

    // Select 10 routes in0 when reset is low.
    check_sel_10_routes_in0: assert property (
        @($global_clock) disable iff (reset)
        (sel == 2'b10) |-> (out == in0)
    );

    // Select 11 routes in3 when reset is low.
    check_sel_11_routes_in3: assert property (
        @($global_clock) disable iff (reset)
        (sel == 2'b11) |-> (out == in3)
    );

    // Changing only in1 does not affect the output.
    check_in1_change_has_no_effect: assert property (
        @($global_clock) disable iff (reset)
        ($stable(reset) && $stable(in0) && $changed(in1) && $stable(in2) && $stable(in3) && $stable(sel))
        |-> $stable(out)
    );

    // Changing only in2 does not affect the output.
    check_in2_change_has_no_effect: assert property (
        @($global_clock) disable iff (reset)
        ($stable(reset) && $stable(in0) && $stable(in1) && $changed(in2) && $stable(in3) && $stable(sel))
        |-> $stable(out)
    );

    // With sel[1] low, changing only sel[0] does not affect the output.
    check_sel0_change_has_no_effect_when_sel1_low: assert property (
        @($global_clock) disable iff (reset)
        ($stable(reset) && (sel[1] == 1'b0) && $stable(sel[1]) && $changed(sel[0]) &&
         $stable(in0) && $stable(in1) && $stable(in2) && $stable(in3))
        |-> $stable(out)
    );

    // With sel[0] low, changing only sel[1] does not affect the output.
    check_sel1_change_has_no_effect_when_sel0_low: assert property (
        @($global_clock) disable iff (reset)
        ($stable(reset) && (sel[0] == 1'b0) && $stable(sel[0]) && $changed(sel[1]) &&
         $stable(in0) && $stable(in1) && $stable(in2) && $stable(in3))
        |-> $stable(out)
    );

endmodule