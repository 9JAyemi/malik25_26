
module func5(A, C);
    input [25:0] A;
    output [25:0] C;

    wire [24:0] sum;  // Internal wire to store the sum of each bit
    wire [24:0] c_out; // Internal wire to store the carry-out of each bit

    // FullAdder module
    FullAdder FA0(.a(A[25]), .b(A[24]), .c_in(1'b0), .sum(sum[24]), .c_out(c_out[24]));
    FullAdder FA1(.a(sum[24]), .b(A[23]), .c_in(c_out[24]), .sum(sum[23]), .c_out(c_out[23]));
    FullAdder FA2(.a(sum[23]), .b(A[22]), .c_in(c_out[23]), .sum(sum[22]), .c_out(c_out[22]));
    FullAdder FA3(.a(sum[22]), .b(A[21]), .c_in(c_out[22]), .sum(sum[21]), .c_out(c_out[21]));
    FullAdder FA4(.a(sum[21]), .b(A[20]), .c_in(c_out[21]), .sum(sum[20]), .c_out(c_out[20]));
    FullAdder FA5(.a(sum[20]), .b(A[19]), .c_in(c_out[20]), .sum(sum[19]), .c_out(c_out[19]));
    FullAdder FA6(.a(sum[19]), .b(A[18]), .c_in(c_out[19]), .sum(sum[18]), .c_out(c_out[18]));
    FullAdder FA7(.a(sum[18]), .b(A[17]), .c_in(c_out[18]), .sum(sum[17]), .c_out(c_out[17]));
    FullAdder FA8(.a(sum[17]), .b(A[16]), .c_in(c_out[17]), .sum(sum[16]), .c_out(c_out[16]));
    FullAdder FA9(.a(sum[16]), .b(A[15]), .c_in(c_out[16]), .sum(sum[15]), .c_out(c_out[15]));
    FullAdder FA10(.a(sum[15]), .b(A[14]), .c_in(c_out[15]), .sum(sum[14]), .c_out(c_out[14]));
    FullAdder FA11(.a(sum[14]), .b(A[13]), .c_in(c_out[14]), .sum(sum[13]), .c_out(c_out[13]));
    FullAdder FA12(.a(sum[13]), .b(A[12]), .c_in(c_out[13]), .sum(sum[12]), .c_out(c_out[12]));
    FullAdder FA13(.a(sum[12]), .b(A[11]), .c_in(c_out[12]), .sum(sum[11]), .c_out(c_out[11]));
    FullAdder FA14(.a(sum[11]), .b(A[10]), .c_in(c_out[11]), .sum(sum[10]), .c_out(c_out[10]));
    FullAdder FA15(.a(sum[10]), .b(A[9]), .c_in(c_out[10]), .sum(sum[9]), .c_out(c_out[9]));
    FullAdder FA16(.a(sum[9]), .b(A[8]), .c_in(c_out[9]), .sum(sum[8]), .c_out(c_out[8]));
    FullAdder FA17(.a(sum[8]), .b(A[7]), .c_in(c_out[8]), .sum(sum[7]), .c_out(c_out[7]));
    FullAdder FA18(.a(sum[7]), .b(A[6]), .c_in(c_out[7]), .sum(sum[6]), .c_out(c_out[6]));
    FullAdder FA19(.a(sum[6]), .b(A[5]), .c_in(c_out[6]), .sum(sum[5]), .c_out(c_out[5]));
    FullAdder FA20(.a(sum[5]), .b(A[4]), .c_in(c_out[5]), .sum(sum[4]), .c_out(c_out[4]));
    FullAdder FA21(.a(sum[4]), .b(A[3]), .c_in(c_out[4]), .sum(sum[3]), .c_out(c_out[3]));
    FullAdder FA22(.a(sum[3]), .b(A[2]), .c_in(c_out[3]), .sum(sum[2]), .c_out(c_out[2]));
    FullAdder FA23(.a(sum[2]), .b(A[1]), .c_in(c_out[2]), .sum(sum[1]), .c_out(c_out[1]));
    FullAdder FA24(.a(sum[1]), .b(A[0]), .c_in(c_out[1]), .sum(C[0]), .c_out(c_out[0]));

    // Assign the carry-out of the last FullAdder to the carry-out of the top-level module
    assign C[25] = c_out[0];

    // Assign the sum of each FullAdder to the output of the top-level module
    assign C[24:1] = sum[24:1];
endmodule
module FullAdder(a, b, c_in, sum, c_out);
    input a, b, c_in;
    output sum, c_out;

    assign sum = a ^ b ^ c_in;
    assign c_out = (a & b) | (c_in & (a ^ b));
endmodule