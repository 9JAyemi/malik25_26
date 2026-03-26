module decoder_3to8 (
    A,
    B,
    C,
    Y0,
    Y1,
    Y2,
    Y3,
    Y4,
    Y5,
    Y6,
    Y7
);

    input A, B, C;
    output Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7;

    wire notA, notB, notC;
    wire and0, and1, and2, and3, and4, and5, and6, and7;

    // Negation of inputs
    not notA (notA, A);
    not notB (notB, B);
    not notC (notC, C);

    // AND gates
    and and0_0 (and0, notA, notB, notC);
    and and11 (and1, notA, notB, C);
    and and22 (and2, notA, B, notC);
    and and33 (and3, notA, B, C);
    and and44 (and4, A, notB, notC);
    and and55 (and5, A, notB, C);
    and and66 (and6, A, B, notC);
    and and77 (and7, A, B, C);

    // Outputs
    assign Y0 = and0;
    assign Y1 = and1;
    assign Y2 = and2;
    assign Y3 = and3;
    assign Y4 = and4;
    assign Y5 = and5;
    assign Y6 = and6;
    assign Y7 = and7;

endmodule