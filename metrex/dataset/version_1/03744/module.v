
module simple_calculator(
    input [7:0] a,
    input [7:0] b,
    input [1:0] op,
    input clk,
    output reg [7:0] out
);

always @(*) begin
    case(op)
        2'b00: out = a + b;
        2'b01: out = a - b;
        2'b10: out = a & b;
        2'b11: out = a | b;
    endcase
end

endmodule