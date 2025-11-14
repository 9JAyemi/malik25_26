
module barrel_shifter (
    input [31:0] data_in,
    input [4:0] shift_amt,
    output [31:0] data_out
);

    assign data_out = data_in >> shift_amt;

endmodule
module adder (
    input [7:0] num1,
    input [7:0] num2,
    output [8:0] sum
);

    assign sum = num1 + num2;

endmodule
module functional_module (
    input [31:0] data_in,
    input [8:0] sum_in,
    output [31:0] final_out
);

    assign final_out = data_in + {{23{1'b0}}, sum_in};

endmodule
module top_module (
    input clk,
    input reset,
    input [31:0] data_in,
    input [4:0] shift_amt,
    input [7:0] num1,
    input [7:0] num2,
    output [31:0] final_out
);

    wire [31:0] shifted_data;
    wire [8:0] sum;

    barrel_shifter shifter (
        .data_in(data_in),
        .shift_amt(shift_amt),
        .data_out(shifted_data)
    );

    adder add (
        .num1(num1),
        .num2(num2),
        .sum(sum)
    );

    functional_module func (
        .data_in(shifted_data),
        .sum_in(sum),
        .final_out(final_out)
    );

endmodule