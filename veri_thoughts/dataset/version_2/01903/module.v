
module four_bit_adder (
    input [3:0] a,
    input [3:0] b,
    input cin,
    output [3:0] sum,
    output cout
);

    wire [3:0] temp_sum;
    wire [3:0] temp_cout;

    // Full adder for the least significant bit
    full_adder fa0(.a(a[0]), .b(b[0]), .cin(cin), .sum(temp_sum[0]), .cout(temp_cout[0]));
    
    // Carry chain for the rest of the bits
    genvar i;
    generate
        for (i = 1; i < 4; i = i + 1) begin : carry_chain
            full_adder fa(.a(a[i]), .b(b[i]), .cin(temp_cout[i - 1]), .sum(temp_sum[i]), .cout(temp_cout[i]));
        end
    endgenerate

    assign sum = temp_sum;
    assign cout = temp_cout[3];
    
endmodule
module full_adder (
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

    wire s1;
    wire c1;
    wire c2;

    xor(s1, a, b);
    xor(sum, s1, cin);
    and(c1, a, b);
    and(c2, s1, cin);
    or(cout, c1, c2);

endmodule