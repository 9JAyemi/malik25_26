
module or4_module (
    input A,
    input B,
    input C,
    input D,
    input vdd,
    input vss,
    output X
);

    wire AB, CD;
    wire ABn, CDn;

    and (AB, A, B);
    and (CD, C, D);
    and (X, AB, CD);

    not (ABn, AB);
    not (CDn, CD);

endmodule
