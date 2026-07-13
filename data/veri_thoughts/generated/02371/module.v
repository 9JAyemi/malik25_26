module shift_register (
    input clk,
    input reset,
    input enable,
    input shift,
    input [7:0] parallel_in,
    output reg [7:0] parallel_out
);

reg [7:0] pipeline_reg [0:2];

always @(posedge clk) begin
    if (reset) begin
        pipeline_reg[0] <= 8'b0;
        pipeline_reg[1] <= 8'b0;
        pipeline_reg[2] <= 8'b0;
    end
    else begin
        pipeline_reg[0] <= enable ? {pipeline_reg[1][6:0], pipeline_reg[2][7]} : pipeline_reg[0];
        pipeline_reg[1] <= enable ? {pipeline_reg[2][6:0], pipeline_reg[0][7]} : pipeline_reg[1];
        pipeline_reg[2] <= enable ? {shift ? parallel_in : pipeline_reg[1][6:0], pipeline_reg[2][7:1]} : pipeline_reg[2];
    end
end

always @* begin
    parallel_out = pipeline_reg[0];
end

endmodule