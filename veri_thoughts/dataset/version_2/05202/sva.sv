module my_comb_sva (
    input logic clk,
    input logic HI,
    input logic LO,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // HI matches the RTL combinational equation.
    check_hi_matches_expr: assert property (
        @(posedge clk)
        HI == ((VPWR || VPB) ? 1'b1 : (VNB ? 1'b0 : (VGND ? 1'b0 : 1'b0)))
    );

    // LO matches the RTL combinational equation.
    check_lo_matches_expr: assert property (
        @(posedge clk)
        LO == ((VGND || VNB) ? 1'b1 : (VPB ? 1'b0 : (VPWR ? 1'b1 : 1'b0)))
    );

    // HI is high whenever VPWR or VPB is high.
    check_hi_high_on_vpwr_or_vpb: assert property (
        @(posedge clk)
        (VPWR || VPB) |-> (HI == 1'b1)
    );

    // HI is low when both VPWR and VPB are low.
    check_hi_low_when_no_vpwr_or_vpb: assert property (
        @(posedge clk)
        (!VPWR && !VPB) |-> (HI == 1'b0)
    );

    // LO is high whenever VGND or VNB is high.
    check_lo_high_on_vgnd_or_vnb: assert property (
        @(posedge clk)
        (VGND || VNB) |-> (LO == 1'b1)
    );

    // LO is low when VPB is high without VGND or VNB overriding it.
    check_lo_low_on_vpb_without_override: assert property (
        @(posedge clk)
        (!VGND && !VNB && VPB) |-> (LO == 1'b0)
    );

    // LO is high when VPWR is high and VPB, VGND, and VNB are low.
    check_lo_high_on_vpwr_only: assert property (
        @(posedge clk)
        (!VGND && !VNB && !VPB && VPWR) |-> (LO == 1'b1)
    );

    // LO is low when all controlling inputs are low.
    check_lo_low_when_all_inputs_low: assert property (
        @(posedge clk)
        (!VGND && !VNB && !VPB && !VPWR) |-> (LO == 1'b0)
    );

endmodule