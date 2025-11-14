
module decoder_4to16_pipeline (
    input A, B,
    output reg [15:0] Y
);

reg [1:0] stage1_A, stage1_B;
reg [3:0] stage2_A, stage2_B;
reg [7:0] stage3_A, stage3_B;

always @(A or B) begin
    stage1_A <= A;
    stage1_B <= B;
end

always @(stage1_A or stage1_B) begin
    stage2_A <= stage1_A;
    stage2_B <= stage1_B;
end

always @(stage2_A or stage2_B) begin
    stage3_A <= stage2_A;
    stage3_B <= stage2_B;
end

always @(stage3_A or stage3_B) begin
    if (stage3_A == 2'b00) begin
        Y <= 16'b0000000000000001;
    end else if (stage3_A == 2'b01) begin
        Y <= 16'b0000000000000010;
    end else if (stage3_A == 2'b10) begin
        Y <= 16'b0000000000000100;
    end else if (stage3_A == 2'b11) begin
        Y <= 16'b1000000000000000;
    end
end

endmodule