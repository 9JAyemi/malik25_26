
module top_module (
    input [3:0] A,
    input [3:0] B,
    input [3:0] C,
    input SEL1,
    input SEL2,
    output [3:0] OUT
);

    wire [3:0] add_sub_out;
    wire [3:0] mux_out;

    adder_subtractor_module add_sub (
        .A(A),
        .B(B),
        .SUB(SEL1),
        .OUT(add_sub_out)
    );

    mux4to1_module mux (
        .IN0(4'b0),
        .IN1(4'b0),
        .IN2(4'b0),
        .IN3(C),
        .SEL(SEL1),
        .OUT(mux_out)
    );

    assign OUT = SEL2 ? mux_out : 4'b0;

endmodule
module adder_subtractor_module (
    input [3:0] A,
    input [3:0] B,
    input SUB,
    output [3:0] OUT
);

    assign OUT = SUB ? A - B : A + B;

endmodule
module mux4to1_module (
    input [3:0] IN0,
    input [3:0] IN1,
    input [3:0] IN2,
    input [3:0] IN3,
    input SEL,
    output [3:0] OUT
);

    assign OUT = SEL ? IN3 : (SEL ? IN2 : (SEL ? IN1 : IN0));

endmodule