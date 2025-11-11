
module clk_1_khz(
    input clk_50mhz,
    output reg clk_1khz
);

reg [3:0] count;

always @(posedge clk_50mhz)
begin
    count <= count + 1;
    if(count == 7) begin // 7 is chosen because 7*143 = 1001
        count <= 0;
        clk_1khz <= ~clk_1khz;
    end
end

endmodule