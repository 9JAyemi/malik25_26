module barrel_shifter (
    input [3:0] A,
    input [3:0] B,
    output reg [3:0] Q
);

reg [3:0] stage1_out;
reg [3:0] stage2_out;

always @(*) begin
    stage1_out = (B[3]) ? {A[2:0], 1'b0} : {1'b0, A[3:1]};
end

always @(*) begin
    stage2_out = (B[2]) ? {stage1_out[1:0], 2'b00} : {2'b00, stage1_out[3:2]};
end

always @(*) begin
    Q = (B[1]) ? {stage2_out[0], stage2_out[3:1]} : {stage2_out[2:0], stage2_out[3]};
end

endmodule