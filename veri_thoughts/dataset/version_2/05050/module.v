module adder_8bit(
    input [7:0] A,
    input [7:0] B,
    output [7:0] sum,
    output carry_out
);

    wire[8:0] temp_sum;

    assign temp_sum = {1'b0, A} + {1'b0, B};

    assign sum = temp_sum[7:0];
    assign carry_out = temp_sum[8];

endmodule