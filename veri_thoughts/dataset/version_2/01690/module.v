
module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    output [3:0] OUT
);

wire [3:0] sum;
wire [3:0] carry;

// First stage
assign {carry[0], sum[0]} = A + B;

// Second stage
assign {carry[1], sum[1]} = sum[0] + carry[0];

// Third stage
assign {carry[2], sum[2]} = sum[1] + carry[1];

// Fourth stage
assign {carry[3], sum[3]} = sum[2] + carry[2];

assign OUT = sum[3:0];

endmodule