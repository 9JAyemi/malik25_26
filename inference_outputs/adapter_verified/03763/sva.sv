module fill_diode_sva (
    input logic clk,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic fill
);

// fill must match the RTL combinational equation.
    check_fill_equation: assert property (
        @(posedge clk) fill == ((VPWR & !VGND) | (!VPB & VNB))
    );

// VPWR high and VGND low must drive fill high.
    check_vpwr_high_vgnd_low: assert property (
        @(posedge clk) (VPWR & !VGND) |-> fill
    );

// VPB low and VNB high must drive fill high.
    check_vpb_low_vnb_high: assert property (
        @(posedge clk) (!VPB & VNB) |-> fill
    );

// Any low-to-high transition on VPWR with VGND low must set fill high.
    check_vpwr_rise_with_vgnd_low: assert property (
        @(posedge clk) $rose(VPWR) && !VGND |-> fill
    );

// Any low-to-high transition on VNB with VPB low must set fill high.
    check_vnb_rise_with_vpb_low: assert property (
        @(posedge clk) $rose(VNB) && !VPB |-> fill
    );

// Any high-to-low transition on VGND with VPWR high must clear fill.
    check_vgnd_fall_with_vpwr_high: assert property (
        @(posedge clk) $fell(VGND) && VPWR |-> !fill
    );

// Any high-to-low transition on VPB with VNB high must clear fill.
    check_vpb_fall_with_vnb_high: assert property (
        @(posedge clk) $fell(VPB) && VNB |-> !fill
    );

endmodule
