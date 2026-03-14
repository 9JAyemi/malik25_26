module counter (
    input clk,
    input rst,
    input [31:0] max_val,
    output reg [31:0] count
);

always @(posedge clk) begin
    if (rst) begin
        count <= 0;
    end else if (count == max_val) begin
        count <= 0;
    end else begin
        count <= count + 1;
    end
end

endmodule