
module final_module(
    input cout_adder, input [2:0] sum_adder,
    input [2:0] out_or_bitwise,
    input out_or_logical,
    input [5:0] out_not,
    output reg [5:0] final_output
);
    wire [2:0] sum_out;

    full_adder fa1(sum_adder[0], out_or_bitwise[0], cout_adder, sum_out[0], );
    full_adder fa2(sum_adder[1], out_or_bitwise[1], , sum_out[1], );
    full_adder fa3(sum_adder[2], out_or_bitwise[2], , sum_out[2], );

    always @(*) begin
        final_output <= sum_out + out_not;
    end
endmodule
module full_adder(
    input a, b, c_in,
    output sum, c_out
);
    assign sum = a ^ b ^ c_in;
    assign c_out = (a & b) | (b & c_in) | (c_in & a);
endmodule