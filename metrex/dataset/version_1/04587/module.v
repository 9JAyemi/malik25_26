
module ripple_carry_adder (
    input [3:0] in0,
    input [3:0] in1,
    input carry_in,
    output [3:0] sum,
    output carry_out
);

wire [3:0] stage1_sum;
wire stage1_carry;

wire [3:0] stage2_sum;
wire stage2_carry;

wire [3:0] stage3_sum;
wire stage3_carry;

// Stage 1
full_adder fa1(in0[0], in1[0], carry_in, stage1_sum[0], stage1_carry);

// Stage 2
full_adder fa2(in0[1], in1[1], stage1_carry, stage2_sum[1], stage2_carry);

// Stage 3
full_adder fa3(in0[2], in1[2], stage2_carry, stage3_sum[2], stage3_carry);

// Stage 4
full_adder fa4(in0[3], in1[3], stage3_carry, sum[3], carry_out);

assign sum[0] = stage1_sum[0];
assign sum[1] = stage2_sum[1];
assign sum[2] = stage3_sum[2];

endmodule

module full_adder (
    input a,
    input b,
    input carry_in,
    output sum,
    output carry_out
);

assign sum = a ^ b ^ carry_in;
assign carry_out = (a & b) | (a & carry_in) | (b & carry_in);

endmodule
