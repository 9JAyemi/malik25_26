module binary_counter (
    input clk,
    input rst,
    output reg [3:0] Q
);

always @(posedge clk) begin
    if (rst) begin
        Q <= 4'b0;
    end else begin
        Q <= Q + 1;
    end
end

endmodule