module counter(
    input clk,
    input reset,
    input [7:0] max_count,
    output reg [7:0] count
);

always @(posedge clk) begin
    if (reset) begin
        count <= 0;
    end else if (count == max_count) begin
        count <= 0;
    end else begin
        count <= count + 1;
    end
end

endmodule