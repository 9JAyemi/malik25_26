
module addsub_8bit(A, B, op, sum, carry_out);

input [7:0] A;
input [7:0] B;
input op;
output [7:0] sum;
output carry_out;

wire [7:0] twos_comp_B;
wire [7:0] temp_sum;

assign carry_out = 1'b0;
assign twos_comp_B = ~B + 1;

addsub_1bit addsub_inst_0(A[0], twos_comp_B[0], op, temp_sum[0]);
addsub_1bit addsub_inst_1(A[1], twos_comp_B[1], op, temp_sum[1]);
addsub_1bit addsub_inst_2(A[2], twos_comp_B[2], op, temp_sum[2]);
addsub_1bit addsub_inst_3(A[3], twos_comp_B[3], op, temp_sum[3]);
addsub_1bit addsub_inst_4(A[4], twos_comp_B[4], op, temp_sum[4]);
addsub_1bit addsub_inst_5(A[5], twos_comp_B[5], op, temp_sum[5]);
addsub_1bit addsub_inst_6(A[6], twos_comp_B[6], op, temp_sum[6]);
addsub_1bit addsub_inst_7(A[7], twos_comp_B[7], op, temp_sum[7]);

assign sum = op ? twos_comp_B : temp_sum;

endmodule
module addsub_1bit(A, B, op, sum);

input A;
input B;
input op;
output sum;

assign sum = A ^ B ^ op;

endmodule