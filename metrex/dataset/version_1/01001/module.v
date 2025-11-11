
module div_clk (
    input clk_in,
    input clk_type,
    input reset,
    output reg clk_out
);

reg clock_div2;
reg [2:0] rst_reg;

always @(posedge clk_in or posedge reset) begin
    if (reset == 1'b1) begin
        rst_reg[0] <= 1'b1;
        rst_reg[1] <= 1'b1;
        rst_reg[2] <= 1'b1;
    end else begin
        rst_reg[0] <= reset;
        rst_reg[1] <= rst_reg[0] & reset;
        rst_reg[2] <= rst_reg[1] & rst_reg[0] & reset;
    end
end

always @(posedge clk_in) 
    clock_div2 <= ~clock_div2;

always @(posedge clk_in or posedge rst_reg[2]) begin
    if (rst_reg[2] == 1'b1)
        clk_out <= 1'b0;
    else if (clk_type == 1'b1)
        clk_out <= clock_div2;
    else
        clk_out <= clk_in;
end

endmodule