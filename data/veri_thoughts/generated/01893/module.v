
module adder_4bit(
    input [3:0] in1,
    input [3:0] in2,
    output [3:0] out,
    output carry
);

wire [3:0] temp_sum;
wire [4:0] temp_carry; // 4 bits for carry

// Generate the sum and carry for each bit
genvar i;
generate
    for (i = 0; i < 4; i = i + 1) begin : bit_adder
        full_adder adder(
            .in1(in1[i]),
            .in2(in2[i]),
            .carry_in(temp_carry[i]),
            .sum(temp_sum[i]),
            .carry_out(temp_carry[i+1])
        );
    end
endgenerate

assign temp_carry[0] = 0; // Initial value for carry_in

// Assign the output and carry
assign out = temp_sum;
assign carry = temp_carry[4];

endmodule
module full_adder(
    input in1,
    input in2,
    input carry_in,
    output sum,
    output carry_out
);

assign sum = in1 ^ in2 ^ carry_in;
assign carry_out = (in1 & in2) | (in1 & carry_in) | (in2 & carry_in);

endmodule