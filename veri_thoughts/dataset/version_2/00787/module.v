module ripple_carry_adder(
    input [99:0] a, b,
    input cin,
    output cout,
    output [99:0] sum );

    wire [100:0] temp_sum;
    wire [99:0] temp_carry;

    assign temp_sum = {1'b0, a} + {1'b0, b} + {1'b0, cin};
    assign temp_carry = temp_sum[100:1];

    assign sum = temp_sum[99:0];
    assign cout = temp_carry[99];

endmodule

module top_module( 
    input [99:0] a, b,
    input cin,
    output cout,
    output [99:0] sum );

    ripple_carry_adder rca(
        .a(a),
        .b(b),
        .cin(cin),
        .cout(cout),
        .sum(sum)
    );

endmodule