module binary_counter
#(parameter n = 4)
(
    input rst,
    input clk,
    output reg [n-1:0] count
);

always @(posedge clk) begin
    if (rst) begin
        count <= 0;
    end
    else if (count == 2**n-1) begin
        count <= 0;
    end
    else begin
        count <= count + 1;
    end
end

endmodule