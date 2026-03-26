module mux_2to1 (
    input A,
    input B,
    input S,
    output Y
);

    assign Y = (S == 1'b0) ? A : B;

endmodule