
module full_adder(
    input A,
    input B,
    input Cin,
    output Cout,
    output Sum
);

    assign Sum = A ^ B ^ Cin;
    assign Cout = (A & B) | (B & Cin) | (Cin & A);

endmodule
module mux2(
    input I0,
    input I1,
    input S,
    output O
);

    assign O = (S) ? I1 : I0;

endmodule