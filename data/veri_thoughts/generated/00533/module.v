module arithmetic_op (
    input [7:0] a,
    input [7:0] b,
    input [1:0] ctrl,
    output reg [7:0] result
);

always @(*) begin
    case(ctrl)
        2'b00: result = a + b;
        2'b01: result = a - b;
        2'b10: result = a & b;
        2'b11: result = a | b;
    endcase
end

endmodule