module pipeline (
    input clk,
    input clk_ena,
    input in_stream,
    input reset,
    output reg pipeline_reg_0,
    output reg pipeline_reg_1,
    output reg pipeline_reg_2,
    output reg pipeline_reg_3,
    output reg pipeline_reg_4,
    output reg pipeline_reg_5,
    output reg pipeline_reg_6,
    output reg pipeline_reg_7,
    output reg pipeline_reg_8,
    output reg pipeline_reg_9,
    output reg pipeline_reg_10,
    output reg pipeline_reg_11,
    output reg pipeline_reg_12,
    output reg pipeline_reg_13,
    output reg pipeline_reg_14,
    output reg pipeline_reg_15,
    output reg pipeline_reg_16
);

always @(posedge clk or posedge reset) begin
    if (reset) begin
        pipeline_reg_0 <= 1'b0;
        pipeline_reg_1 <= 1'b0;
        pipeline_reg_2 <= 1'b0;
        pipeline_reg_3 <= 1'b0;
        pipeline_reg_4 <= 1'b0;
        pipeline_reg_5 <= 1'b0;
        pipeline_reg_6 <= 1'b0;
        pipeline_reg_7 <= 1'b0;
        pipeline_reg_8 <= 1'b0;
        pipeline_reg_9 <= 1'b0;
        pipeline_reg_10 <= 1'b0;
        pipeline_reg_11 <= 1'b0;
        pipeline_reg_12 <= 1'b0;
        pipeline_reg_13 <= 1'b0;
        pipeline_reg_14 <= 1'b0;
        pipeline_reg_15 <= 1'b0;
        pipeline_reg_16 <= 1'b0;
    end else begin
        if (clk_ena) begin
            pipeline_reg_0 <= in_stream;
            pipeline_reg_1 <= pipeline_reg_0;
            pipeline_reg_2 <= pipeline_reg_1;
            pipeline_reg_3 <= pipeline_reg_2;
            pipeline_reg_4 <= pipeline_reg_3;
            pipeline_reg_5 <= pipeline_reg_4;
            pipeline_reg_6 <= pipeline_reg_5;
            pipeline_reg_7 <= pipeline_reg_6;
            pipeline_reg_8 <= pipeline_reg_7;
            pipeline_reg_9 <= pipeline_reg_8;
            pipeline_reg_10 <= pipeline_reg_9;
            pipeline_reg_11 <= pipeline_reg_10;
            pipeline_reg_12 <= pipeline_reg_11;
            pipeline_reg_13 <= pipeline_reg_12;
            pipeline_reg_14 <= pipeline_reg_13;
            pipeline_reg_15 <= pipeline_reg_14;
            pipeline_reg_16 <= pipeline_reg_15;
        end
    end
end

endmodule