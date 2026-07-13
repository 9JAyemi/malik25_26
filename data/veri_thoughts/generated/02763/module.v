module and4b (
    input  A_N ,
    input  B   ,
    input  C   ,
    input  D   ,
    output X   ,
    input  VPB ,
    input  VPWR,
    input  VGND,
    input  VNB
);
    wire AB, CD, ABCD;
    
    // AND gates for AB and CD
    and gate_AB(AB, A_N, B);
    and gate_CD(CD, C, D);
    
    // AND gate for ABCD
    and gate_ABCD(ABCD, AB, CD);
    
    // Inverter for X
    not inv_X(X, ABCD);
    
endmodule