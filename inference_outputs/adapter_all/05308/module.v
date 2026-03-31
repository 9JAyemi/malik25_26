
module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    output reg [3:0] sum
);

    wire [3:0] temp_sum;
    wire [3:0] temp_carry;

    // Full adder for least significant bit
    full_adder FA0(.a(A[0]), .b(B[0]), .cin(1'b0), .sum(temp_sum[0]), .cout(temp_carry[0]));

    // Full adder for second least significant bit
    full_adder FA1(.a(A[1]), .b(B[1]), .cin(temp_carry[0]), .sum(temp_sum[1]), .cout(temp_carry[1]));

    // Full adder for third least significant bit
    full_adder FA2(.a(A[2]), .b(B[2]), .cin(temp_carry[1]), .sum(temp_sum[2]), .cout(temp_carry[2]));

    // Full adder for most significant bit
    full_adder FA3(.a(A[3]), .b(B[3]), .cin(temp_carry[2]), .sum(temp_sum[3]), .cout(temp_carry[3]));

    // Combine temporary variables to form 4-bit sum
    always @ (temp_sum)
        sum = temp_sum;

endmodule

module full_adder(
    input a,
    input b,
    input cin,
    output reg sum,
    output reg cout
);

    always @ (a or b or cin)
        begin
            sum = a ^ b ^ cin;
            cout = (a & b) | (a & cin) | (b & cin);
        end

endmodule
