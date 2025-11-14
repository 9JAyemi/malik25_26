module counter(
    input clk,
    input rst,
    input en,
    input [15:0] max_count,
    output reg [15:0] count
);

always @(posedge clk) begin
    if (rst) begin
        count <= 0;
    end else if (en) begin
        if (count == max_count) begin
            count <= 0;
        end else begin
            count <= count + 1;
        end
    end
end

endmodule