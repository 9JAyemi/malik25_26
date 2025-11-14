
module custom_module (
    A1,
    A2,
    A3,
    A4,
    B1,
    X
);

    input A1;
    input A2;
    input A3;
    input A4;
    input B1;
    output X;

    wire X1;
    wire X2;

    and (X1, A1, A2);
    and (X2, A3, A4);
    nor (X, X1, X2, B1);

endmodule