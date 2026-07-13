module adder(
    input signed [31:0] a,
    input signed [31:0] b,
    input clk,
    output reg signed [31:0] sum
);

reg signed [31:0] temp_sum;
reg overflow;

always @(posedge clk) begin
    temp_sum = a + b;
    overflow = (a[31] == b[31]) && (temp_sum[31] != a[31]);
    if (overflow) begin
        if (a[31] == 1) begin
            sum <= -2147483648; // minimum value for 32-bit signed two's complement
        end else begin
            sum <= 2147483647; // maximum value for 32-bit signed two's complement
        end
    end else begin
        sum <= temp_sum;
    end
end

endmodule