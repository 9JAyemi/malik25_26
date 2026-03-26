module XOR2(
    input a,
    input b,
    output c
);

    assign c = a ^ b;

endmodule

module XOR3(
    input i0,
    input i1,
    input i2,
    output o
);

    wire w1, w2;

    XOR2 x1(
        .a(i0),
        .b(i1),
        .c(w1)
    );

    XOR2 x2(
        .a(w1),
        .b(i2),
        .c(o)
    );

endmodule