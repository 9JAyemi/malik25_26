module adder_with_carry(
    input [3:0] a,
    input [3:0] b,
    input cin,
    output [3:0] sum,
    output cout
);

wire [3:0] temp_sum; // intermediate sum
wire c1, c2, c3; // carry signals

// full adder for least significant bit
full_adder fa0(.a(a[0]), .b(b[0]), .cin(cin), .sum(temp_sum[0]), .cout(c1));

// full adder for second bit
full_adder fa1(.a(a[1]), .b(b[1]), .cin(c1), .sum(temp_sum[1]), .cout(c2));

// full adder for third bit
full_adder fa2(.a(a[2]), .b(b[2]), .cin(c2), .sum(temp_sum[2]), .cout(c3));

// full adder for most significant bit
full_adder fa3(.a(a[3]), .b(b[3]), .cin(c3), .sum(temp_sum[3]), .cout(cout));

assign sum = temp_sum; // assign intermediate sum to output

endmodule

// full adder module
module full_adder(
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

wire s1, s2, s3; // intermediate signals

// XOR gate for sum
assign s1 = a ^ b;
assign sum = s1 ^ cin;

// AND gate for carry-out
assign s2 = a & b;
assign s3 = cin & s1;
assign cout = s2 | s3;

endmodule