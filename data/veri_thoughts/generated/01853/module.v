
module my_xor3 (
    A,
    B,
    C,
    X
);

    input A;
    input B;
    input C;
    output X;

    wire xor1_out;
    wire xor2_out;

    xor gate1 (xor1_out, A, B);
    xor gate2 (xor2_out, xor1_out, C);

    assign X = xor2_out;

endmodule
