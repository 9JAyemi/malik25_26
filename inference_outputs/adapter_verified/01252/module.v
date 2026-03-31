
module inverter(
    input  I,
    output O
);
    assign O = ~I;
endmodule
module and_gate(
    input  A,
    input  B,
    output Y
);
    assign Y = A & B;
endmodule
module mux_2to1(
    input  A,
    input  B,
    input  S,
    output Y
);
    wire not_A = ~A;
    wire not_B = ~B;
    wire and_out1 = not_A & S;
    wire and_out2 = not_B & ~S;

    assign Y = and_out1 | and_out2;
endmodule