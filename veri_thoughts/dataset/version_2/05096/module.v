module mux_2to1(
    input wire A0,
    input wire A1,
    input wire S,
    output wire X
);

assign X = (S == 0) ? A0 : A1;

endmodule