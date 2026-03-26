module bitwise_and (
    input clk,
    input [31:0] A,
    input [31:0] B,
    output reg [31:0] Q
);

always @(posedge clk) begin
    Q <= A & B;
end

endmodule