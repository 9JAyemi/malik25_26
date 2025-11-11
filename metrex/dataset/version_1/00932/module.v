
module my_logic_gate (
    Y   ,
    A1  ,
    A2  ,
    B1  ,
    C1  ,
    D1 
);

    output Y   ;
    input  A1  ;
    input  A2  ;
    input  B1  ;
    input  C1  ;
    input  D1  ;


    wire and1;
    wire and2;
    wire or1;

    and base(
        .Y(and1),
        .A(A1),
        .B(A2),
        .C(B1),
        .D(C1),
        .E(D1)
    );

    and and_gate1(
        .Y(and2),
        .A(B1),
        .B(C1),
        .C(D1)
    );

    or or_gate1(
        .Y(Y),
        .A(and1),
        .B(and2)
    );

endmodule