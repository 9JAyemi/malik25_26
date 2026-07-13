
module SyncCounter(
    input clk,
    input rst,
    output reg [3:0] count,
    output [3:0] leds
);

always @(posedge clk) begin
    if (rst) begin
        count <= 4'b0;
    end else begin
        count <= count + 1;
    end
end

assign leds = count;

endmodule
