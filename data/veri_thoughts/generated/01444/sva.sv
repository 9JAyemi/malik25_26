module mux4to1_using_2to1_sva (
    input logic clk,             // Sampling clock for SVA (DUT is combinational)
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic [3:0] out
);
    // DUT analysis: no clock/reset in RTL; purely combinational 4:1 mux built from 2:1 stages.

    ///// Functional routing rules /////
    // When sel == 2'b00, out must equal in0.
    check_sel00_routes_in0: assert property (
        @(posedge clk) (sel === 2'b00) |-> ##0 (out == in0)
    );
    // When sel == 2'b01, out must equal in1.
    check_sel01_routes_in1: assert property (
        @(posedge clk) (sel === 2'b01) |-> ##0 (out == in1)
    );
    // When sel == 2'b10, out must equal in2.
    check_sel10_routes_in2: assert property (
        @(posedge clk) (sel === 2'b10) |-> ##0 (out == in2)
    );
    // When sel == 2'b11, out must equal in3.
    check_sel11_routes_in3: assert property (
        @(posedge clk) (sel === 2'b11) |-> ##0 (out == in3)
    );

    ///// Combinational stability and causality /////
    // If all inputs and sel are stable, out must be stable.
    check_out_stable_if_all_inputs_stable: assert property (
        @(posedge clk) ($stable(in0) && $stable(in1) && $stable(in2) && $stable(in3) && $stable(sel)) |-> ##0 $stable(out)
    );
    // If out changed, at least one input or sel must have changed.
    check_out_change_has_cause: assert property (
        @(posedge clk) $changed(out) |-> ##0 (!$stable({in0,in1,in2,in3,sel}))
    );

    ///// Non-selected inputs do not affect out /////
    // With sel==00 and sel/in0 stable, out must remain stable.
    check_no_effect_others_when_00: assert property (
        @(posedge clk) (sel === 2'b00 && $stable(sel) && $stable(in0)) |-> ##0 $stable(out)
    );
    // With sel==01 and sel/in1 stable, out must remain stable.
    check_no_effect_others_when_01: assert property (
        @(posedge clk) (sel === 2'b01 && $stable(sel) && $stable(in1)) |-> ##0 $stable(out)
    );
    // With sel==10 and sel/in2 stable, out must remain stable.
    check_no_effect_others_when_10: assert property (
        @(posedge clk) (sel === 2'b10 && $stable(sel) && $stable(in2)) |-> ##0 $stable(out)
    );
    // With sel==11 and sel/in3 stable, out must remain stable.
    check_no_effect_others_when_11: assert property (
        @(posedge clk) (sel === 2'b11 && $stable(sel) && $stable(in3)) |-> ##0 $stable(out)
    );

endmodule