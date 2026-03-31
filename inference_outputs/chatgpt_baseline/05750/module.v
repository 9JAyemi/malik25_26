module mux_2_1(
    input A,
    input B,
    input SEL,
    output Y
);

    assign Y = SEL ? B : A;

endmodule