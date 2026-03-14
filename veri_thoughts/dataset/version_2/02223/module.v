module larger_number(
    input [3:0] num1,
    input [3:0] num2,
    output reg [3:0] larger
);

reg [3:0] stage1_num1;
reg [3:0] stage1_num2;
reg [1:0] stage2_result;

always @(num1) begin
    stage1_num1 <= num1;
end

always @(num2) begin
    stage1_num2 <= num2;
end

always @(stage1_num1, stage1_num2) begin
    if (stage1_num1 > stage1_num2) begin
        stage2_result <= 2'b01;
    end else if (stage1_num1 < stage1_num2) begin
        stage2_result <= 2'b10;
    end else begin
        stage2_result <= 2'b00;
    end
end

always @(stage2_result, stage1_num1, stage1_num2) begin
    if (stage2_result == 2'b01) begin
        larger <= stage1_num1;
    end else if (stage2_result == 2'b10) begin
        larger <= stage1_num2;
    end else begin
        larger <= stage1_num1;
    end
end

endmodule