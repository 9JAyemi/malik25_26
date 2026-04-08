module sky130_fd_sc_ms__mux_2_1 (
    out ,
    in0 ,
    in1 ,
    sel ,
    VPWR,
    VGND,
    VPB ,
    VNB
);

    output out ;
    input  in0 ;
    input  in1 ;
    input  sel ;
    input  VPWR;
    input  VGND;
    input  VPB ;
    input  VNB ;
    
    assign out = sel ? in1 : in0;

endmodule