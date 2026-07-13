
module mux_4_1 (
    input a,
    input b,
    input c,
    input d,
    input s0,
    input s1,
    output y
);

    wire m0_out;
    wire m1_out;

    // First 2-to-1 MUX
    mux2_1 mux0 (
        .a(a),
        .b(b),
        .sel(s0),
        .y(m0_out)
    );

    // Second 2-to-1 MUX
    mux2_1 mux1 (
        .a(c),
        .b(d),
        .sel(s0),
        .y(m1_out)
    );

    // Final 2-to-1 MUX
    mux2_1 mux2 (
        .a(m0_out),
        .b(m1_out),
        .sel(s1),
        .y(y)
    );

endmodule

module mux2_1 (
    input a,
    input b,
    input sel,
    output y
);

    assign y = sel ? b : a;

endmodule
