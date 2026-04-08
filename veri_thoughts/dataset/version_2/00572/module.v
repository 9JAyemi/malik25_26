module input_pipeline (
    clk,
    clk_ena,
    in_stream,
    pipeline_reg_0,
    pipeline_reg_1,
    pipeline_reg_2,
    pipeline_reg_3,
    pipeline_reg_4,
    pipeline_reg_5,
    pipeline_reg_6,
    pipeline_reg_7,
    pipeline_reg_8,
    pipeline_reg_9,
    pipeline_reg_10,
    pipeline_reg_11,
    reset
);

    parameter WIDTH = 1;

    input clk;
    input clk_ena;
    input [WIDTH-1:0] in_stream;
    output [WIDTH-1:0] pipeline_reg_0;
    output [WIDTH-1:0] pipeline_reg_1;
    output [WIDTH-1:0] pipeline_reg_2;
    output [WIDTH-1:0] pipeline_reg_3;
    output [WIDTH-1:0] pipeline_reg_4;
    output [WIDTH-1:0] pipeline_reg_5;
    output [WIDTH-1:0] pipeline_reg_6;
    output [WIDTH-1:0] pipeline_reg_7;
    output [WIDTH-1:0] pipeline_reg_8;
    output [WIDTH-1:0] pipeline_reg_9;
    output [WIDTH-1:0] pipeline_reg_10;
    output [WIDTH-1:0] pipeline_reg_11;
    input reset;

    reg [WIDTH-1:0] pipeline_reg_0;
    reg [WIDTH-1:0] pipeline_reg_1;
    reg [WIDTH-1:0] pipeline_reg_2;
    reg [WIDTH-1:0] pipeline_reg_3;
    reg [WIDTH-1:0] pipeline_reg_4;
    reg [WIDTH-1:0] pipeline_reg_5;
    reg [WIDTH-1:0] pipeline_reg_6;
    reg [WIDTH-1:0] pipeline_reg_7;
    reg [WIDTH-1:0] pipeline_reg_8;
    reg [WIDTH-1:0] pipeline_reg_9;
    reg [WIDTH-1:0] pipeline_reg_10;
    reg [WIDTH-1:0] pipeline_reg_11;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            pipeline_reg_0 <= 0;
            pipeline_reg_1 <= 0;
            pipeline_reg_2 <= 0;
            pipeline_reg_3 <= 0;
            pipeline_reg_4 <= 0;
            pipeline_reg_5 <= 0;
            pipeline_reg_6 <= 0;
            pipeline_reg_7 <= 0;
            pipeline_reg_8 <= 0;
            pipeline_reg_9 <= 0;
            pipeline_reg_10 <= 0;
            pipeline_reg_11 <= 0;
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
            end
        end
    end

endmodule