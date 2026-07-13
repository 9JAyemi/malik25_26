module and4 (
    output Y,
    input A, B, C, D
);

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire w1, w2, w3;
    
    and u1 (w1, A, B);
    and u2 (w2, C, D);
    and u3 (w3, w1, w2);
    
    assign Y = w3;

endmodule