module full_adder (
    input A,
    input B,
    input Cin,
    output Sum,
    output Cout
);

    wire w1, w2, w3;

    assign w1 = A ^ B;
    assign w2 = w1 ^ Cin;
    assign Sum = w2;

    assign w3 = A & B;
    assign Cout = w3 | (Cin & w1);

endmodule