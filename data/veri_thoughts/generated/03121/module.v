
module calculator(
    input [7:0] in1,
    input [7:0] in2,
    input [1:0] op,
    output reg [7:0] out
);

always @(*) begin
    case(op)
        2'b00: out = in1 + in2; // addition
        2'b01: out = in1 - in2; // subtraction
        2'b10: out = in1 * in2; // multiplication
        2'b11: out = in1 / in2; // division
        default: out = 8'b0; // default case
    endcase
end

endmodule