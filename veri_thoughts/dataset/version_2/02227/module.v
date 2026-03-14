
module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    output [3:0] Y
);

    wire [3:0] sum;
    wire carry0, carry1, carry2, carry;

    // Full adder
    // Takes three inputs (a, b, and carry_in) and returns two outputs (sum and carry_out)
    // Implements the following logic:
    // sum = a ^ b ^ carry_in
    // carry_out = (a & b) | (a & carry_in) | (b & carry_in)
    // where ^ is the XOR operator and & is the AND operator
    // This is a basic verilog construct
    // The full adder is used to add the four bits of A and B to produce the four bits of Y
    // The carry output of each full adder is fed as the carry_in input to the next full adder
    // The carry output of the last full adder is the final carry output of the module
    // The sum output of each full adder is one of the four bits of the output Y
    // The four bits of Y are concatenated to form the final output
    // This is also a basic verilog construct
    // The following code implements the four-bit adder using four full adders
    // The full adders are instantiated using the module instance syntax

    full_adder fa0(.a(A[0]), .b(B[0]), .carry_in(1'b0), .sum(sum[0]), .carry_out(carry0));
    full_adder fa1(.a(A[1]), .b(B[1]), .carry_in(carry0), .sum(sum[1]), .carry_out(carry1));
    full_adder fa2(.a(A[2]), .b(B[2]), .carry_in(carry1), .sum(sum[2]), .carry_out(carry2));
    full_adder fa3(.a(A[3]), .b(B[3]), .carry_in(carry2), .sum(sum[3]), .carry_out(carry));

    assign Y = {sum[3], sum[2], sum[1], sum[0]};

endmodule
module full_adder(
    input a,
    input b,
    input carry_in,
    output sum,
    output carry_out
);

    assign sum = a ^ b ^ carry_in;
    assign carry_out = (a & b) | (a & carry_in) | (b & carry_in);

endmodule