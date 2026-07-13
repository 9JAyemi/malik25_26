
module binary_counter(
    input clk, rst, en,
    output reg [3:0] count,
    output reg max
);

always @(posedge clk, posedge rst)
begin
    if (rst)
        count <= 4'b0;
    else if (en)
        count <= count + 1;
end

always @(*) begin
    if (count == 4'b1111)
        max = 1'b1;
    else
        max = 1'b0;
end

endmodule
