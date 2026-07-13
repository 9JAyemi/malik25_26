module mux_2to1 (
    A,
    B,
    SEL,
    Y
);

    // Module ports
    input A;
    input B;
    input SEL;
    output Y;

    // Implement 2:1 MUX
    assign Y = (SEL == 1'b1) ? A : B;

endmodule