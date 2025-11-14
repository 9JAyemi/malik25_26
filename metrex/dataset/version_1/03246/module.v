
module nor_gate (
    input a,
    input b,
    output out
);
    assign out = !(a & b);
endmodule

module full_adder (
    input a,
    input b,
    input cin,
    output cout,
    output sum
);
    wire g, p;
    assign sum = a ^ b ^ cin;
    assign g = a & b;
    assign p = a & cin;
    assign cout = g | p;
endmodule

module bitwise_and (
    input [1:0] a,
    input [1:0] b,
    output [1:0] out
);
    assign out = {1'b0, a[0] & b[0]}; // Fix the bit widths
endmodule

module top_module (
    input a,
    input b,
    input cin,
    output cout,
    output sum,
    output [1:0] final_output
);
    wire nor_out;
    nor_gate n1 (.a(a), .b(b), .out(nor_out));
    full_adder fa1 (.a(a), .b(b), .cin(cin), .cout(cout), .sum(sum));
    bitwise_and ba1 (.a({1'b0, nor_out}), .b({1'b0, sum}), .out(final_output)); // Fix the bit widths
endmodule
