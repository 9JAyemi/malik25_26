
module magnitude_comparator_4bit (
    input [3:0] A, B,
    output EQ, GT, LT
);

wire [4:0] sum;
wire EQ_int, GT_int, LT_int;

pipeline_stage1 stage1(
    .A(A),
    .B(B),
    .sum(sum)
);

pipeline_stage2 stage2(
    .sum(sum),
    .EQ(EQ_int),
    .GT(GT_int),
    .LT(LT_int)
);

assign EQ = EQ_int;
assign GT = GT_int;
assign LT = LT_int;

endmodule
module pipeline_stage1 (
    input [3:0] A, B,
    output reg [4:0] sum
);

wire [3:0] A_xor_B;
wire [3:0] A_and_B;

assign A_xor_B = A ^ B;
assign A_and_B = A & B;

always @(*) begin
    sum[4] = A[3] ^ B[3];
    sum[3] = A_and_B[2];
    sum[2] = A_xor_B[2] ^ A_and_B[1];
    sum[1] = A_xor_B[1] ^ A_and_B[0];
    sum[0] = A_xor_B[0];
end

endmodule
module pipeline_stage2 (
    input [4:0] sum,
    output reg EQ, GT, LT
);

wire [4:0] sum_abs;

assign sum_abs = (sum[4] == 1) ? ~sum + 5'b1 : sum;

always @(*) begin
    EQ = (sum_abs == 5'b0) ? 1'b1 : 1'b0;
    GT = (sum_abs[4] == 1) ? 1'b0 : 1'b1;
    LT = (sum_abs[4] == 1) ? 1'b1 : 1'b0;
end

endmodule