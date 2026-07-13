module buffer_3input (
    Z   ,
    A   ,
    B   ,
    C   ,
    TE_B
);

    output Z   ;
    input  A   ;
    input  B   ;
    input  C   ;
    input  TE_B;

    wire sel1, sel2;

    assign sel1 = (A & ~B & ~C) | (~A & B & ~C) | (~A & ~B & C);
    assign sel2 = (A & B & ~C) | (A & ~B & C) | (~A & B & C);

    assign Z = TE_B & (sel1 | sel2) & (A | B | C);

endmodule