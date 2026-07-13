module bitwise_or(
    input [7:0] A,
    input [7:0] B,
    input enable,
    input clk,
    output reg [7:0] result
);

reg [7:0] temp_result;

always @(*) begin
    if (enable) begin
        temp_result = A | B;
    end
end

always @(posedge clk) begin
    result <= temp_result;
end

endmodule