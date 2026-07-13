module XOR3_sva(
    input logic clk,
    input logic i0,
    input logic i1,
    input logic i2,
    input logic o
);

    // No RTL clock or reset; clk is the assertion sampling clock.
    // XOR3 is purely combinational.

    // Output equals the XOR of all three inputs.
    check_output_is_three_input_xor: assert property (
        @(posedge clk) o == (i0 ^ i1 ^ i2)
    );

    // With i2 low, the output reduces to i0 XOR i1.
    check_reduce_when_i2_low: assert property (
        @(posedge clk) (i2 == 1'b0) |-> (o == (i0 ^ i1))
    );

    // With i2 high, the output is the inverse of i0 XOR i1.
    check_invert_when_i2_high: assert property (
        @(posedge clk) (i2 == 1'b1) |-> (o == ~(i0 ^ i1))
    );

    // Equal i0 and i1 make the output match i2.
    check_equal_inputs_pass_through_i2: assert property (
        @(posedge clk) (i0 == i1) |-> (o == i2)
    );

    // Different i0 and i1 make the output invert i2.
    check_different_inputs_invert_i2: assert property (
        @(posedge clk) (i0 != i1) |-> (o == ~i2)
    );

    // With i0 low, the output reduces to i1 XOR i2.
    check_reduce_when_i0_low: assert property (
        @(posedge clk) (i0 == 1'b0) |-> (o == (i1 ^ i2))
    );

    // With i1 low, the output reduces to i0 XOR i2.
    check_reduce_when_i1_low: assert property (
        @(posedge clk) (i1 == 1'b0) |-> (o == (i0 ^ i2))
    );

endmodule