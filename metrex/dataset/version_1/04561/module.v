module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    input [7:0] a,
    input [7:0] b,
    input select, // Select input to choose between adder1 and adder2
    output [7:0] out
);

reg [7:0] sum1, sum2;

always @(posedge clk) begin
    if (reset) begin
        sum1 <= 8'b0;
        sum2 <= 8'b0;
    end else begin
        if (select) begin
            sum1 <= a + b;
        end else begin
            sum2 <= a + b;
        end
    end
end

assign out = select ? sum1 : sum2;

endmodule