module addition(
    input [7:0] a,
    input [7:0] b,
    output [7:0] sum,
    output overflow
);

wire [8:0] temp_sum;
wire carry;

assign temp_sum = {1'b0, a} + {1'b0, b}; // Add a and b, include a carry bit
assign sum = temp_sum[7:0]; // Output the sum
assign carry = temp_sum[8]; // Check if there was an overflow

assign overflow = (a[7] == b[7] && sum[7] != a[7]) || (a[7] != b[7] && sum[7] == carry);

endmodule