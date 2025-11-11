
module nor_gate (
    input  A,
    input  B,
    output Y
);

    assign Y = ~(A | B);

endmodule

module pwrgood_pp (
    input  A,
    input  B,
    input  C,
    output Y
);

    assign Y = (A & B) | C;

endmodule

module custom_module (
    input  A1,
    input  A2,
    input  B1,
    input  Vdd,
    input  Gnd,
    output X
);

    wire nor0_out;
    wire nor1_out_X;
    wire pwrgood_pp_out_X;

    nor_gate nor0 (
        .A(A1),
        .B(A2),
        .Y(nor0_out)
    );

    nor_gate nor1 (
        .A(B1),
        .B(nor0_out),
        .Y(nor1_out_X)
    );

    pwrgood_pp pwrgood_pp (
        .A(Vdd),
        .B(nor1_out_X),
        .C(Gnd),
        .Y(pwrgood_pp_out_X)
    );

    assign X = pwrgood_pp_out_X; // Remove the buffer

endmodule
