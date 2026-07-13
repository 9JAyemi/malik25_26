
module d_ff_sr (clk, rst, set, d, q);
input clk, rst, set, d;
output reg q;

always @(posedge clk, negedge rst) begin
    if (!rst) begin
        q <= 1'b0;
    end else if (set) begin
        q <= 1'b1;
    end else begin
        q <= d;
    end
end

endmodule