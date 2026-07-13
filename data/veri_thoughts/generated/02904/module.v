
module sky130_fd_sc_hd__and4b (
    X   ,
    A_N ,
    B   ,
    C   ,
    D   ,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    // Module ports
    output X   ;
    input  A_N ;
    input  B   ;
    input  C   ;
    input  D   ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;

    // Local signals
    wire not0_out         ;
    wire and0_out_X       ;

    // Inverter
    not not0 (not0_out, A_N);

    // 3-input AND gate
    and and0 (and0_out_X, not0_out, B, C, D);

    // Buffer
    buf buf0 (X, and0_out_X);

endmodule