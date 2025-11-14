module calculator(
    input clk,
    input op,
    input [3:0] num1,
    input [3:0] num2,
    output reg [3:0] result
);

always @(posedge clk) begin
    if (op == 0) begin
        result <= num1 + num2;
    end else begin
        result <= num1 - num2;
    end
end

endmodule