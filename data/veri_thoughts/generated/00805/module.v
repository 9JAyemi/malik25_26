module counter_3bit_async_reset(
    input clk,
    input rst,
    output reg [2:0] count
);

always @(posedge clk or negedge rst) begin
    if (!rst) begin
        count <= 3'b0;
    end else begin
        count <= count + 1;
    end
end

endmodule