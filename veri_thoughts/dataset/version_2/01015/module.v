module nor4(
    input A,
    input B,
    input C,
    input D,
    output Y
);

wire n1, n2, n3;

nor u1 (
    n1,
    A,
    B
);

nor u2 (
    n2,
    C,
    D
);

nor u3 (
    n3,
    n1,
    n2
);

assign Y = n3;

endmodule