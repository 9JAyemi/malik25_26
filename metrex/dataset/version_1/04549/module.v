
module adder_4bit_carry(
    input [3:0] a,
    input [3:0] b,
    input cin,
    output [3:0] sum,
    output cout
);

wire [3:0] half_sum;
wire [3:0] full_sum;

// First half adder
assign half_sum[0] = a[0] ^ b[0];
assign cout = a[0] & b[0];

// Full adder
genvar i;
generate
    for (i = 1; i < 4; i = i + 1) begin : adder_loop
        assign half_sum[i] = a[i] ^ b[i];
        assign full_sum[i] = (a[i] & b[i]) | (a[i] & full_sum[i-1]) | (b[i] & full_sum[i-1]);
    end
endgenerate

// Final sum
assign sum = half_sum ^ {3'b0, cin}; // cin is added to the LSB of the sum

endmodule