
module four_bit_adder (
    A,
    B,
    Cin,
    Sum,
    Cout
);

    input [3:0] A;
    input [3:0] B;
    input Cin;
    output [3:0] Sum;
    output Cout;

    wire [3:0] Xor1;
    wire [3:0] Xor2;
    wire [3:0] And1;
    wire [3:0] And2;
    wire [3:0] Or1;
    wire [3:0] Or2;
    wire [3:0] Or3;
    wire [3:0] Not1;
    wire [3:0] Not2;

    assign Xor1 = A ^ B;
    assign And1 = A & B;
    assign Xor2 = Xor1 ^ Cin;
    assign And2 = Xor1 & Cin;
    assign Sum = Xor2;
    assign Cout = And1 | And2;

endmodule
