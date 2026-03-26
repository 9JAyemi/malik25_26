
module sky130_fd_sc_lp__dfxtp_lp (
    Q   ,
    CLK ,
    D   ,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    output Q   ;
    input  CLK ;
    input  D   ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;

    reg Q;

    always @(posedge CLK) begin
        Q <= D;
    end

    buf b1 (Q, Q);

endmodule