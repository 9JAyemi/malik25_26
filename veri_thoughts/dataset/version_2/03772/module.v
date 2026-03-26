
module mux4to1_using_full_adders (
    input [3:0] in0,
    input [3:0] in1,
    input [3:0] in2,
    input [3:0] in3,
    input [1:0] sel,
    output [3:0] out
);

wire [3:0] add1_out, add2_out, add3_out;

// Pipeline stage 1
full_adder fa1(in0[0], in1[0], sel[0], add1_out[0], );
full_adder fa2(in0[1], in1[1], sel[0], add1_out[1], );
full_adder fa3(in0[2], in1[2], sel[0], add1_out[2], );
full_adder fa4(in0[3], in1[3], sel[0], add1_out[3], );

// Pipeline stage 2
full_adder fa5(in2[0], in3[0], sel[0], add2_out[0], );
full_adder fa6(in2[1], in3[1], sel[0], add2_out[1], );
full_adder fa7(in2[2], in3[2], sel[0], add2_out[2], );
full_adder fa8(in2[3], in3[3], sel[0], add2_out[3], );

// Pipeline stage 3
full_adder fa9(add1_out[0], add2_out[0], sel[1], add3_out[0], out[0]);
full_adder fa10(add1_out[1], add2_out[1], sel[1], add3_out[1], out[1]);
full_adder fa11(add1_out[2], add2_out[2], sel[1], add3_out[2], out[2]);
full_adder fa12(add1_out[3], add2_out[3], sel[1], add3_out[3], out[3]);

endmodule
module full_adder (
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

wire cin_temp;
assign cin_temp = a ^ b;
assign sum = cin_temp ^ cin;
assign cout = (a & b) | (cin & cin_temp);

endmodule