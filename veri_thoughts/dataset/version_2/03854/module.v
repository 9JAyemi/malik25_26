
module ripple_carry_adder (
    COUT,
    SUM ,
    A   ,
    B   ,
    CIN 
);

    output COUT;
    output [3:0] SUM ;
    input  [3:0] A   ;
    input  [3:0] B   ;
    input  CIN ;
    
    wire [3:0] carry;
    
    full_adder fa0 (
        .COUT(carry[0]),
        .SUM(SUM[0]),
        .A(A[0]),
        .B(B[0]),
        .CIN(CIN)
    );
    
    full_adder fa1 (
        .COUT(carry[1]),
        .SUM(SUM[1]),
        .A(A[1]),
        .B(B[1]),
        .CIN(carry[0])
    );
    
    full_adder fa2 (
        .COUT(carry[2]),
        .SUM(SUM[2]),
        .A(A[2]),
        .B(B[2]),
        .CIN(carry[1])
    );
    
    full_adder fa3 (
        .COUT(COUT),
        .SUM(SUM[3]),
        .A(A[3]),
        .B(B[3]),
        .CIN(carry[2])
    );

endmodule

module full_adder (
    COUT,
    SUM ,
    A   ,
    B   ,
    CIN 
);

    output COUT;
    output SUM ;
    input  A   ;
    input  B   ;
    input  CIN ;

    assign SUM = A ^ B ^ CIN;
    assign COUT = (A & B) | (A & CIN) | (B & CIN);

endmodule
