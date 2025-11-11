
module Adder (
    input [7:0] a,
    input [7:0] b,
    output [8:0] sum
);

    wire [7:0] carry;
    wire [7:0] half_sum;

    // Generate the carry bit for each bit of the sum
    assign carry[0] = 1'b0;
    genvar i;
    for (i = 1; i < 8; i = i + 1) begin
        assign carry[i] = (a[i-1] & b[i-1]) | (a[i-1] & carry[i-1]) | (b[i-1] & carry[i-1]);
    end

    // Generate the half-sum for each bit of the sum
    assign half_sum[0] = a[0] ^ b[0];
    for (i = 1; i < 8; i = i + 1) begin
        assign half_sum[i] = a[i] ^ b[i] ^ carry[i-1];
    end

    // Combine the carry and half-sum to form the final sum
    assign sum[8] = carry[7]; //MSB
    assign sum[7:0] = {half_sum, 1'b0}; //LSB
endmodule
