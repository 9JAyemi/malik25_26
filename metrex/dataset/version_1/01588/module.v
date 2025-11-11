module nor3 (
    output Y,
    input A,
    input B,
    input C
);

    assign Y = ~(A | B | C);

endmodule

module nor4 (
    output Y,
    input A,
    input B,
    input C,
    input D
);
    
    wire n1, n2, n3, n4, n5, n6;
    
    nor3 n3_1 (
        .Y(n1),
        .A(A),
        .B(B),
        .C(C)
    );
    
    nor3 n3_2 (
        .Y(n2),
        .A(B),
        .B(C),
        .C(D)
    );
    
    nor3 n3_3 (
        .Y(n3),
        .A(A),
        .B(C),
        .C(D)
    );
    
    nor3 n3_4 (
        .Y(n4),
        .A(A),
        .B(B),
        .C(D)
    );
    
    nor3 n3_5 (
        .Y(n5),
        .A(n1),
        .B(n2),
        .C(n3)
    );
    
    nor3 n3_6 (
        .Y(Y),
        .A(n5),
        .B(n4),
        .C(D)
    );

endmodule