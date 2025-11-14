
module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    input carry_in,
    input clk,
    output [3:0] sum,
    output carry_out
);

reg [3:0] A_reg, B_reg, sum_reg;
reg carry_in_reg, carry_out_reg;

always @(posedge clk) begin
    A_reg <= A;
    B_reg <= B;
    carry_in_reg <= carry_in;
    sum_reg <= A_reg + B_reg + carry_in_reg;
    carry_out_reg <= (A_reg[3] & B_reg[3]) | (A_reg[3] & carry_in_reg) | (B_reg[3] & carry_in_reg);
end

assign sum = sum_reg;
assign carry_out = carry_out_reg;

endmodule