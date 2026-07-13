
module nand_gate(
    input a,
    input b,
    output reg y
);

always @ (a, b) begin
    y = ~(a & b);
end

endmodule
module decoder_2to4(
    input [1:0] in,
    output [3:0] out
);

wire n1, n2;

nand_gate nand1(
    .a(in[0]), 
    .b(in[1]), 
    .y(n1)
);

nand_gate nand2(
    .a(in[0]), 
    .b(~in[1]), 
    .y(n2)
);

assign out = {~n1 & ~n2, ~n1 & n2, n1 & ~n2, n1 & n2};

endmodule