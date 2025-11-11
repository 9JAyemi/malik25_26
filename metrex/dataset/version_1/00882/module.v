module mux_2to1(input [1:0] data, input ctrl, output reg out);

reg [1:0] stage1_data;
reg stage1_ctrl;

always @(*) begin
    stage1_data <= data;
    stage1_ctrl <= ctrl;
end

reg [1:0] stage2_data;
reg stage2_ctrl;

always @(*) begin
    stage2_data <= stage1_data;
    stage2_ctrl <= stage1_ctrl;
end

reg [1:0] stage3_data;
reg stage3_ctrl;

always @(*) begin
    stage3_data <= stage2_data;
    stage3_ctrl <= stage2_ctrl;
end

reg [1:0] stage4_data;
reg stage4_ctrl;

always @(*) begin
    stage4_data <= stage3_data;
    stage4_ctrl <= stage3_ctrl;
end

always @(*) begin
    case (stage4_ctrl)
        1'b0: out <= stage4_data[0];
        1'b1: out <= stage4_data[1];
    endcase
end

endmodule