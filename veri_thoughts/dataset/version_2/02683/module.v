module binary_counter #(parameter N = 4) (
    input clk,
    input rst,
    output reg [N-1:0] count
);

always @(posedge clk or negedge rst) begin
    if (rst == 0) begin
        count <= 0;
    end else begin
        count <= count + 1;
    end
end

endmodule