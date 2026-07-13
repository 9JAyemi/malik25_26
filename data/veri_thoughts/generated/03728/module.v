
module top_module (
    input [3:0] A,
    input [3:0] B,
    input [2:0] OP,
    output [3:0] Y
);

    wire [3:0] S;
    wire [3:0] bitwise_Y;
    wire [3:0] functional_Z;

    adder adder_inst (
        .A(A),
        .B(B),
        .S(S)
    );

    bitwise bitwise_inst (
        .A(A),
        .B(B),
        .OP(OP),
        .Y(bitwise_Y)
    );

    functional functional_inst (
        .S(S),
        .Y(bitwise_Y),
        .OP(OP),
        .Z(functional_Z)
    );

    assign Y = (OP == 3'b000) ? S :
               (OP == 3'b001) ? S :
               (OP == 3'b010) ? bitwise_Y :
               (OP == 3'b011) ? bitwise_Y :
               (OP == 3'b100) ? bitwise_Y :
               4'b0;

endmodule

module adder (
    input [3:0] A,
    input [3:0] B,
    output [3:0] S
);

    assign S = A + B;

endmodule

module bitwise (
    input [3:0] A,
    input [3:0] B,
    input [2:0] OP,
    output [3:0] Y
);

    assign Y = (OP == 3'b010) ? A & B :
               (OP == 3'b011) ? A | B :
               (OP == 3'b100) ? A ^ B :
               4'b0;

endmodule

module functional (
    input [3:0] S,
    input [3:0] Y,
    input [2:0] OP,
    output [3:0] Z
);

    assign Z = (OP == 3'b000) ? S :
               (OP == 3'b001) ? S :
               (OP == 3'b010) ? Y :
               (OP == 3'b011) ? Y :
               (OP == 3'b100) ? Y :
               4'b0;

endmodule
