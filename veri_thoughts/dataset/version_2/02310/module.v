
module nor2_pg (
    output Y,
    input A,
    input B,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    // Local signals
    wire nor_out_Y;

    // NOR gate implementation
    assign nor_out_Y = A & B;

    // Power good functionality
    power_good #(
        .PWRGOOD_WIDTH(1)
    ) \pwrgood_pp0 (
        .Y(Y),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );

endmodule
module power_good #(
    parameter PWRGOOD_WIDTH = 1
)(
    output [PWRGOOD_WIDTH - 1:0] Y,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    assign Y = (VPWR > VGND) ? VPB : VNB;

endmodule