module adder_subtractor(
    input [3:0] A, B,
    input C,
    output [3:0] S,
    output Cout
);

wire [3:0] B_neg;
assign B_neg = (~B) + 1;

assign S = (C) ? (A + B_neg) : (A + B);
assign Cout = (C) ? (A >= B) : (A + B >= 16);

endmodule
