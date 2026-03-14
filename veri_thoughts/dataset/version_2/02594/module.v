
module counter_4bit_with_async_reset (
    input clk,
    input reset,
    output reg [3:0] Q
);

always @(posedge clk or posedge reset) begin
    if (reset) begin
        Q <= 0;
    end else begin
        Q <= Q + 1;
    end
end

endmodule
