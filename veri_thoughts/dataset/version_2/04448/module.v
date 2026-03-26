
module alu (
    input [3:0] a,
    input [3:0] b,
    input [2:0] op,
    output reg [3:0] out,
    input clk
);

reg [3:0] a_reg, b_reg, alu_out_reg;

always @(posedge clk) begin
    a_reg <= a;
    b_reg <= b;
    case(op)
        3'b000: alu_out_reg <= a_reg + b_reg; // addition
        3'b001: alu_out_reg <= a_reg - b_reg; // subtraction
        3'b010: alu_out_reg <= a_reg & b_reg; // bitwise AND
        3'b011: alu_out_reg <= a_reg | b_reg; // bitwise OR
        3'b100: alu_out_reg <= a_reg ^ b_reg; // bitwise XOR
        3'b101: alu_out_reg <= {a_reg[2:0], 1'b0}; // shift left
        default: alu_out_reg <= 4'b0;
    endcase
end

always @(posedge clk) begin
    out <= alu_out_reg;
end

endmodule
