module binary_adder (
    input a, b, // 2 input bits for the binary numbers
    input carry_in, // Carry-in input for the half adder
    output sum, // Output for the sum of the two bits
    output carry_out // Output for the carry-out of the half adder
);

    assign sum = a ^ b ^ carry_in;
    assign carry_out = (a & b) | (carry_in & (a ^ b));

endmodule

module top_module (
    input a1, b1, a2, b2, // 4 input bits for the two binary numbers
    input select, // Select input to choose between carry-out of first half adder and second half adder
    output [1:0] sum // 2-bit output for the sum of the two binary numbers
);

    wire carry1, carry2;
    wire sum1, sum2;

    binary_adder adder1(a1, b1, 1'b0, sum1, carry1);
    binary_adder adder2(a2, b2, 1'b0, sum2, carry2);

    assign sum = {select ? carry2 : carry1, sum1} + sum2;

endmodule