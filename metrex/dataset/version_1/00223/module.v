module mux2 (
    X ,
    A0,
    A1,
    S
);

    output X ;
    input  A0;
    input  A1;
    input  S ;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    assign X = (S == 1'b1) ? A1 : A0;

endmodule