module adder(
    input [7:0] A,
    input [7:0] B,
    input Cin,
    output [7:0] Sum,
    output Cout
);

wire [8:0] temp;

assign temp = A + B + Cin;

assign Sum = temp[7:0];
assign Cout = (temp > 255) ? 1 : 0;

endmodule

