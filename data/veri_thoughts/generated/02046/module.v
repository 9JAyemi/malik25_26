module and4_pwr_good (
    output X,
    output pwrgood_pp0_out_X,
    input A_N,
    input B,
    input C,
    input D,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    // Local signals
    wire not0_out;
    wire and0_out_X;

    // Invert A_N input
    assign not0_out = ~A_N;

    // Perform AND operation on inputs B, C, and D
    assign and0_out_X = not0_out & B & C & D;

    // Create power good output
    assign pwrgood_pp0_out_X = and0_out_X & VPWR & VGND;

    // Buffer output to X
    assign X = pwrgood_pp0_out_X;

endmodule