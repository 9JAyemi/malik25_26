module mux_2to1_enable (
    input A,
    input B,
    input EN,
    output Y
);

    assign Y = EN ? A : B;

endmodule