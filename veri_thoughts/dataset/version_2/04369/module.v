module sky130_fd_sc_hd__lpflow_bleeder (
    SHORT,
    VPWR ,
    VGND ,
    VPB  ,
    VNB
);

    input SHORT;
    inout VPWR ;
    input VGND ;
    input VPB  ;
    input VNB  ;

    assign VPWR = (SHORT) ? VGND : (VPB - VNB);

endmodule