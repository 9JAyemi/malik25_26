module binary_counter #(
    parameter n = 4 // Change to desired number of bits
)(
    input clk,
    input reset,
    input enable,
    output reg [n-1:0] count
);

always @(posedge clk) begin
    if (reset) begin
        count <= 0;
    end else if (enable) begin
        count <= count + 1;
    end
end

endmodule