
module adder_mux (
    input [3:0] a,
    input [3:0] b,
    input control,
    output [3:0] sum
);

    wire [3:0] sum1, sum2;
    
    // First 4-bit adder
    four_bit_adder adder1(.a(a), .b(b), .sum(sum1));
    
    // Second 4-bit adder
    four_bit_adder adder2(.a(a), .b(b), .sum(sum2));
    
    // 2-to-1 multiplexer
    assign sum = control ? sum2 : sum1;
    
endmodule

module four_bit_adder (
    input [3:0] a,
    input [3:0] b,
    output [3:0] sum
);

    wire c1, c2, c3;

    full_adder adder0(.a(a[0]), .b(b[0]), .cin(0), .sum(sum[0]), .cout(c1));
    full_adder adder1(.a(a[1]), .b(b[1]), .cin(c1), .sum(sum[1]), .cout(c2));
    full_adder adder2(.a(a[2]), .b(b[2]), .cin(c2), .sum(sum[2]), .cout(c3));
    full_adder adder3(.a(a[3]), .b(b[3]), .cin(c3), .sum(sum[3]), .cout());

endmodule

module full_adder (
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    assign sum = a ^ b ^ cin;
    assign cout = (a & b) | (a & cin) | (b & cin);

endmodule
