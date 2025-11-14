
module simple_calc(
    input [7:0] a,
    input [7:0] b,
    input op,
    output reg [7:0] sum,
    output reg [7:0] diff
);

reg [8:0] temp_diff;
reg [8:0] temp_sum;

always @(*) begin
    if(op) begin
        temp_diff = a - b;
        temp_sum = a + b;
    end
    else begin
        temp_diff = b - a;
        temp_sum = a + b;
    end
end

always @* begin
    diff = temp_diff[7:0];
    sum = temp_sum[7:0];
end

endmodule