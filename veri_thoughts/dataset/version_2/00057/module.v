module adder_4bit(
    input [3:0] A,
    input [3:0] B,
    input reset,
    output [3:0] S
);

wire [3:0] carry;
wire [3:0] sum;

// Implement full-adder for each bit
full_adder fa0(A[0], B[0], reset, carry[0], sum[0]);
full_adder fa1(A[1], B[1], carry[0], carry[1], sum[1]);
full_adder fa2(A[2], B[2], carry[1], carry[2], sum[2]);
full_adder fa3(A[3], B[3], carry[2], carry[3], sum[3]);

// Assign output
assign S = sum;

endmodule

module full_adder(
    input a,
    input b,
    input cin,
    output reg cout,
    output reg sum
);

always @(*) begin
    sum = a ^ b ^ cin;
    cout = (a & b) | (a & cin) | (b & cin);
end

endmodule