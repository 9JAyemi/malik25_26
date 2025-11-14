module mux_2to1(
    input a, b, c, d,
    output x, y, z
);

assign x = c ? a : b;
assign y = c ? b : a;
assign z = c ? d : b;

endmodule