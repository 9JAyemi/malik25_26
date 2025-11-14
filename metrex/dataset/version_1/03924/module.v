module and_gate (
    input  CLK  ,
    input  D    ,
    output Q    ,
    output Q_N  ,
    input  SCD  ,
    input  SCE  ,
    input  SET_B,
    input  VPWR ,
    input  VGND
);

    wire and_output;
    
    assign Q_N = ~Q;

    assign and_output = D & SCD & SET_B & VPWR & VGND;

    assign Q = SCE ? and_output : 1'b0;

endmodule