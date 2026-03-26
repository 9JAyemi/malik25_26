
module or4 (
    input wire A,
    input wire B,
    input wire C,
    input wire D,
    output wire Y
);

    wire AB, CD;

    // First level of OR gates
    or2 or_AB (A, B, AB);
    or2 or_CD (C, D, CD);

    // Second level of OR gate
    assign Y = AB | CD;

endmodule
module or2 (
    input wire A,
    input wire B,
    output wire Y
);

    assign Y = A | B;

endmodule