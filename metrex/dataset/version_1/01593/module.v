module counter(
    input reset,
    input clk,
    output reg [7:0] count
);

always @(posedge clk) begin
    if (reset) begin
        count <= 0;
    end else if (count == 255) begin
        count <= 0;
    end else begin
        count <= count + 1;
    end
end

endmodule