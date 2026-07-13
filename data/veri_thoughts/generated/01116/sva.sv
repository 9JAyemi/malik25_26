module clock_gating_sva (
    input logic CLK,
    input logic GATE,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB,
    input logic GCLK
);
    ///// Clock gating behavior /////
    // When CLK is high (posedge), GCLK equals GATE.
    check_gclk_eq_gate_on_clk_high: assert property (
        @(posedge CLK) (GCLK == GATE)
    );

    // When CLK is low (negedge), GCLK is forced low.
    check_gclk_low_on_clk_low: assert property (
        @(negedge CLK) (GCLK == 1'b0)
    );

    // A rising GATE across posedges produces a rising GCLK across posedges.
    check_gclk_rises_with_gate_rise: assert property (
        @(posedge CLK) $rose(GATE) |-> $rose(GCLK)
    );

    // A falling GATE across posedges produces a falling GCLK across posedges.
    check_gclk_falls_with_gate_fall: assert property (
        @(posedge CLK) $fell(GATE) |-> $fell(GCLK)
    );
endmodule