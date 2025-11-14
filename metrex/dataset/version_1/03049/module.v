module adder (
    input [3:0] a,
    input [3:0] b,
    input enable,
    input reset,
    input clk,
    output reg [3:0] sum
);

    reg [3:0] carry;
    
    always @(posedge clk) begin
        if (reset) begin
            sum <= 4'b0;
            carry <= 4'b0;
        end
        else if (enable) begin
            {carry, sum} <= a + b + carry;
        end
        else begin
            sum <= 4'b0;
            carry <= 4'b0;
        end
    end

endmodule