module adder (
    input [7:0] a,
    input [7:0] b,
    output [7:0] sum,
    output overflow
);

wire [8:0] sum_wire = a + b;
assign overflow = sum_wire[8];
assign sum = sum_wire[7:0];

endmodule

