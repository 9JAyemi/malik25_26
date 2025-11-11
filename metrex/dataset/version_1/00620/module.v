
module adder_4bit (
    input [3:0] a,
    input [3:0] b,
    input cin,
    output [3:0] sum,
    output cout
);

    wire [2:0] carry;

    // First bit
    assign sum[0] = a[0] ^ b[0];
    assign carry[0] = (a[0] & b[0]) | (a[0] & cin) | (b[0] & cin);

    // Second bit
    assign sum[1] = a[1] ^ b[1] ^ carry[0];
    assign carry[1] = (a[1] & b[1]) | ((a[1] | b[1]) & carry[0]);

    // Third bit
    assign sum[2] = a[2] ^ b[2] ^ carry[1];
    assign carry[2] = (a[2] & b[2]) | ((a[2] | b[2]) & carry[1]);

    // Fourth bit
    assign sum[3] = a[3] ^ b[3] ^ carry[2];
    assign cout = carry[2];

endmodule
