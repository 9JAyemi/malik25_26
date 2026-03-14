module mux_2to1(
    input A0,
    input A1,
    input S,
    output X
);

assign X = (S == 1'b0) ? A0 : A1;

endmodule