
module top_module (
    input wire [2:0] a,
    input wire [2:0] b,
    output wire sum_carry_out,
    output wire [2:0] sum,
    output wire carry_out,
    output wire [5:0] sum_decimal
);

    // Splitting the input numbers into separate 1-bit binary numbers
    wire [2:0] a_1, b_1;
    splitter splitter_inst(.in_a(a), .in_b(b), .out_a(a_1), .out_b(b_1));

    // Adding the two 3-bit binary numbers using a half adder
    wire [2:0] sum_half_adder;
    wire carry_out_half_adder;
    half_adder half_adder_inst1(.a(a_1[0]), .b(b_1[0]), .sum(sum_half_adder[0]), .carry_out(carry_out_half_adder));
    half_adder half_adder_inst2(.a(a_1[1]), .b(b_1[1]), .sum(sum_half_adder[1]), .carry_out());
    half_adder half_adder_inst3(.a(a_1[2]), .b(b_1[2]), .sum(sum_half_adder[2]), .carry_out(carry_out));

    // Combining the separate 1-bit binary numbers of the sum using the same logic circuit as in problem 1
    wire [5:0] sum_decimal_logic_circuit;
    logic_circuit logic_circuit_inst(.in(sum_half_adder), .out(sum_decimal_logic_circuit));

    // Outputting the sum and carry-out of the addition as well as the separate 1-bit binary numbers of the sum
    assign sum = sum_half_adder;
    assign sum_carry_out = {carry_out_half_adder, sum_half_adder};
    assign sum_decimal = sum_decimal_logic_circuit;

endmodule
module splitter (
    input wire [2:0] in_a,
    input wire [2:0] in_b,
    output wire [2:0] out_a,
    output wire [2:0] out_b
);

    assign out_a = in_a;
    assign out_b = in_b;

endmodule
module half_adder (
    input wire a,
    input wire b,
    output wire sum,
    output wire carry_out
);

    assign {carry_out, sum} = a + b;

endmodule
module logic_circuit (
    input wire [2:0] in,
    output wire [5:0] out
);

    assign out = in;

endmodule