
module sky130_fd_sc_lp__invkapwr (
    Y,
    A
);

    output Y;
    input  A;

    // Voltage supply signals
    supply1 VPWR ;
    supply0 VGND ;
    supply1 KAPWR;
    supply1 VPB  ;
    supply0 VNB  ;

    // Inverter circuit
    assign Y = ~A;

endmodule