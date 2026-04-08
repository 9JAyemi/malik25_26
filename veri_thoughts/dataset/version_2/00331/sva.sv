module voltage_supply_sva (
    input logic clk,
    input logic rst,
    input logic enable,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // VPWR is initialized high and never reassigned.
    check_vpwr_const_high: assert property (
        @(posedge clk) disable iff (rst) VPWR == 1'b1
    );

    // VGND is initialized low and never reassigned.
    check_vgnd_const_low: assert property (
        @(posedge clk) disable iff (rst) VGND == 1'b0
    );

    // The first active clock after reset keeps both body-bias outputs low.
    check_post_reset_body_bias_low: assert property (
        @(posedge clk) disable iff (rst) $past(rst) |-> (VPB == 1'b0 && VNB == 1'b0)
    );

    // Every active cycle drives VNB low by the next clock.
    check_vnb_forced_low_every_cycle: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> VNB == 1'b0
    );

    // When enable is low, the next clock drives both body-bias outputs low.
    check_disable_clears_body_bias: assert property (
        @(posedge clk) disable iff (rst) !enable |=> (VPB == 1'b0 && VNB == 1'b0)
    );

    // When enable is high, the next clock still keeps VNB low.
    check_enable_keeps_vnb_low: assert property (
        @(posedge clk) disable iff (rst) enable |=> VNB == 1'b0
    );

endmodule