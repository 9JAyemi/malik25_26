module sky130_fd_sc_lp__inputiso1n_sva (
    input logic A,
    input logic SLEEP_B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);
    // No clock or reset in DUT; purely combinational; sample on edges of inputs/outputs.

    // X must equal !A & !SLEEP_B & !VPWR & !VGND & !VPB & !VNB on any input/output edge.
    check_function_on_any_edge: assert property (
        @(posedge A or negedge A or
          posedge SLEEP_B or negedge SLEEP_B or
          posedge VPWR or negedge VPWR or
          posedge VGND or negedge VGND or
          posedge VPB or negedge VPB or
          posedge VNB or negedge VNB or
          posedge X or negedge X)
        X == (!A && !SLEEP_B && !VPWR && !VGND && !VPB && !VNB)
    );

    // If X rises, all inputs must be 0.
    check_x_rise_requires_all_low: assert property (
        @(posedge X) (A == 1'b0) && (SLEEP_B == 1'b0) && (VPWR == 1'b0) && (VGND == 1'b0) && (VPB == 1'b0) && (VNB == 1'b0)
    );

    // If any input falls such that all become 0, X must be 1.
    check_x_high_when_all_low_on_any_fall: assert property (
        @(negedge A or negedge SLEEP_B or negedge VPWR or negedge VGND or negedge VPB or negedge VNB)
        ((A == 1'b0) && (SLEEP_B == 1'b0) && (VPWR == 1'b0) && (VGND == 1'b0) && (VPB == 1'b0) && (VNB == 1'b0)) |-> (X == 1'b1)
    );

    // A high forces X low.
    check_x_low_when_A_high: assert property (
        @(posedge A) X == 1'b0
    );

    // SLEEP_B high forces X low.
    check_x_low_when_SLEEP_B_high: assert property (
        @(posedge SLEEP_B) X == 1'b0
    );

    // VPWR high forces X low.
    check_x_low_when_VPWR_high: assert property (
        @(posedge VPWR) X == 1'b0
    );

    // VGND high forces X low.
    check_x_low_when_VGND_high: assert property (
        @(posedge VGND) X == 1'b0
    );

    // VPB high forces X low.
    check_x_low_when_VPB_high: assert property (
        @(posedge VPB) X == 1'b0
    );

    // VNB high forces X low.
    check_x_low_when_VNB_high: assert property (
        @(posedge VNB) X == 1'b0
    );

endmodule