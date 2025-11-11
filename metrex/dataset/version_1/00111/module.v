
module barrel_shifter (
    input [7:0] A,
    input signed [2:0] B,
    output reg [7:0] Y
);

reg [7:0] stage1_out;
reg [7:0] stage2_out;
reg [7:0] stage3_out;

always @(*) begin
    stage1_out = (B[0] == 1'b1) ? {A[6:0], 1'b0} : {1'b0, A[7:1]};
end

always @(*) begin
    stage2_out = (B[1] == 1'b1) ? {stage1_out[5:0], 2'b00} : {2'b00, stage1_out[7:2]};
end

always @(*) begin
    stage3_out = (B[2] == 1'b1) ? {stage2_out[3:0], 4'b0000} : {4'b0000, stage2_out[7:4]};
end

always @(*) begin
    case (B)
        3'b000 : Y = A;
        3'b001 : Y = stage1_out;
        3'b010 : Y = {A[1:0], A[7:2]};
        3'b011 : Y = {A[2:0], A[7:3]};
        3'b111 : Y = stage3_out;
        3'b110 : Y = {A[4:0], A[7:5]};
        3'b101 : Y = {A[5:0], A[7:6]};
        default: Y = 8'b0;
    endcase
end

endmodule