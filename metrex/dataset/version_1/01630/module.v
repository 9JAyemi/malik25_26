
module add8 (
    input [7:0] A,
    input [7:0] B,
    input signed_unsigned,
    output [7:0] sum,
    output carry_out
);

    wire [8:0] temp_sum;
    assign temp_sum = A + B + {1'b0, signed_unsigned};
    assign {carry_out, sum} = temp_sum;

endmodule