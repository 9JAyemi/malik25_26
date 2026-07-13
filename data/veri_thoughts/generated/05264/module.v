
module full_adder(
    input A, B, CI,
    output SUM, COUT
);

    wire COUT_N;
    sky130_fd_sc_lp__fahcon_1 full_adder_instance (
        .A(A),
        .B(B),
        .CI(CI),
        .SUM(SUM),
        .COUT_N(COUT_N),
        .VPWR(1'b1),
        .VGND(1'b0),
        .VPB(1'b0),
        .VNB(1'b0)
    );
    
    assign COUT = CI & ~COUT_N;
    
endmodule
module sky130_fd_sc_lp__fahcon_1(
    input A, B, CI,
    output SUM, COUT_N,
    input VPWR, VGND, VPB, VNB
);

    assign {COUT_N, SUM} = A + B + CI;

endmodule