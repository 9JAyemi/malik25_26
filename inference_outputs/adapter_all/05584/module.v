

module ClockDivider (
    Divisor,
    clkOut,
    clk,
    rst
);
input [31:0] Divisor;
output clkOut;
wire clkOut;
input clk;
input rst;

reg [31:0] count_i;
reg clkOut_i;



always @(posedge clk, posedge rst) begin: CLOCKDIVIDER_COUNTER
    if (rst) begin
        count_i <= 0;
    end
    else if (($signed({1'b0, count_i}) == ($signed({1'b0, Divisor}) - 1))) begin
        count_i <= 0;
    end
    else begin
        count_i <= (count_i + 1);
    end
end


always @(posedge clk, posedge rst) begin: CLOCKDIVIDER_CLOCKTICK
    if (rst) begin
        clkOut_i <= 0;
    end
    else if (($signed({1'b0, count_i}) == ($signed({1'b0, Divisor}) - 1))) begin
        clkOut_i <= (!clkOut_i);
    end
    else begin
        clkOut_i <= clkOut_i;
    end
end



assign clkOut = clkOut_i;

endmodule
