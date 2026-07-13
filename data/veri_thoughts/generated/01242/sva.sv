module adder_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [8:0] c
);
    // c equals a + b as a 9-bit unsigned sum.
    check_sum_9bit: assert property (
        @(posedge clk) c == ({1'b0, a} + {1'b0, b})
    );

    // Lower 8 bits of c equal 8-bit sum of a and b.
    check_lower_byte: assert property (
        @(posedge clk) c[7:0] == (a + b)
    );

    // Carry bit equals wrap-around detection from 8-bit addition.
    check_carry_wrap: assert property (
        @(posedge clk) c[8] == ((a + b) < a)
    );

    // Sum is at least a (unsigned).
    check_ge_a: assert property (
        @(posedge clk) c >= {1'b0, a}
    );

    // Sum is at least b (unsigned).
    check_ge_b: assert property (
        @(posedge clk) c >= {1'b0, b}
    );

    // Adding zero on b leaves a unchanged.
    check_identity_b_zero: assert property (
        @(posedge clk) (b == 8'h00) |-> (c == {1'b0, a})
    );

    // Adding zero on a leaves b unchanged.
    check_identity_a_zero: assert property (
        @(posedge clk) (a == 8'h00) |-> (c == {1'b0, b})
    );

    // LSB of sum is XOR of operand LSBs.
    check_lsb_xor: assert property (
        @(posedge clk) c[0] == (a[0] ^ b[0])
    );

    // Bit1 sum equals XOR of operand bit1 with carry from bit0.
    check_bit1_sum: assert property (
        @(posedge clk) c[1] == ((a[1] ^ b[1]) ^ (a[0] & b[0]))
    );

    // Sum range is within 0..510.
    check_sum_range: assert property (
        @(posedge clk) c <= 9'd510
    );
endmodule