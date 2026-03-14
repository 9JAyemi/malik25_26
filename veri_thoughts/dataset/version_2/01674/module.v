module sky130_fd_sc_hdll__sdfxtp (
    Q   ,
    CLK ,
    D   ,
    SCD ,
    SCE ,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    output Q   ;
    input  CLK ;
    input  D   ;
    input  SCD ;
    input  SCE ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;

    reg Q;

    always @(posedge CLK or negedge VGND) begin
        if (VGND == 0) begin
            Q <= 0;
        end else if (SCD == 1) begin
            Q <= 1;
        end else if (SCE == 1) begin
            Q <= 0;
        end else begin
            Q <= D;
        end
    end

endmodule

module sky130_fd_sc_hdll__sdfxtp_1 (
    Q   ,
    CLK ,
    D   ,
    SCD ,
    SCE ,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    output Q   ;
    input  CLK ;
    input  D   ;
    input  SCD ;
    input  SCE ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;
    sky130_fd_sc_hdll__sdfxtp base (
        .Q(Q),
        .CLK(CLK),
        .D(D),
        .SCD(SCD),
        .SCE(SCE),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );

endmodule