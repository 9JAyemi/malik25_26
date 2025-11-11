module count_ones (
    input [31:0] in,
    input clk,
    output reg [5:0] out
);

reg [31:0] in_reg;
reg [31:0] in_reg_pipe1;
reg [31:0] in_reg_pipe32;

reg [31:0] sum_reg;
reg [31:0] sum_reg_pipe31;
reg [31:0] sum_reg_pipe32;

always @(posedge clk) begin
    in_reg_pipe1 <= in_reg;
    in_reg_pipe32 <= in_reg_pipe1;
    
    sum_reg_pipe31 <= sum_reg;
    sum_reg_pipe32 <= sum_reg_pipe31;
end

always @(posedge clk) begin
    in_reg <= in;
    sum_reg <= sum_reg_pipe31 + in_reg_pipe32;
end

always @(*) begin
    out = sum_reg_pipe32[5:0];
end

endmodule