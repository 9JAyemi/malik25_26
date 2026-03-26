module my_module (
    Y ,
    A1,
    A2,
    A3,
    B1,
    C1
);

    output Y ;
    input  A1;
    input  A2;
    input  A3;
    input  B1;
    input  C1;

    wire S1, S2, S3, S4, S5;

    // Implement S1 and S2
    assign S1 = A1 & ~A2;
    assign S2 = ~A1 & A2;

    // Implement S3 and S4
    assign S3 = ~B1 & C1;
    assign S4 = B1 & C1;

    // Implement S5
    assign S5 = ~S1 & ~S2 & ~S3 & ~S4;

    // Implement Y
    assign Y = (A1 & A2 & ~A3) | (B1 & ~C1) | (S1 & S2 & ~S3 & ~S4) | S5;

endmodule