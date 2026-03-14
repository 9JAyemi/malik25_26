
module d_ff_reset_preset(clk, reset, preset, d, q);
input clk, reset, preset, d;
output reg q;

always @(posedge clk)
begin
    if (!reset)
        q <= 1'b0;
    else if (!preset)
        q <= 1'b1;
    else
        q <= d;
end

endmodule