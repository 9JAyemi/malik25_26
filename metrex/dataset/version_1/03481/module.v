
module binary_multiplier(clk, reset, a, b, result);

input clk, reset;
input [7:0] a, b;
output reg [15:0] result;
reg [3:0] i;

always @(posedge clk) begin
    if (reset) begin
        result <= 0;
    end else begin
        for (i = 0; i < 8; i = i + 1) begin
            if (a[i]) begin
                result <= result + (b << i);
            end
        end
    end
end

endmodule