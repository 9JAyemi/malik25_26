module mux_2to1(
    input A,
    input B,
    input S,
    output Y
);

assign Y = (~S & A) | (S & B);

endmodule