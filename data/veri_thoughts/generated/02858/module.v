module nor3 (
    input  A,
    input  B,
    input  C,
    output Y
);

    // NOR gate implementation
    assign Y = ~(A | B | C);

endmodule