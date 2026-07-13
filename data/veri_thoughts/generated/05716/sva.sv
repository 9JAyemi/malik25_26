module full_adder_sva (
    input logic clk,
    input logic x_in,
    input logic y_in,
    input logic c_in,
    input logic s_out,
    input logic c_out,
    input logic wire_sum0,
    input logic wire_carry0,
    input logic wire_carry1
);

    // RTL is combinational with no native reset; clk is a sampling clock.

    // First half adder sum is x_in XOR y_in.
    check_u0_sum_xor: assert property (
        @(posedge clk) wire_sum0 == (x_in ^ y_in)
    );

    // First half adder carry is x_in AND y_in.
    check_u0_carry_and: assert property (
        @(posedge clk) wire_carry0 == (x_in & y_in)
    );

    // Second half adder sum is wire_sum0 XOR c_in.
    check_u1_sum_xor: assert property (
        @(posedge clk) s_out == (wire_sum0 ^ c_in)
    );

    // Second half adder carry is wire_sum0 AND c_in.
    check_u1_carry_and: assert property (
        @(posedge clk) wire_carry1 == (wire_sum0 & c_in)
    );

    // Final carry is the OR of the two internal carries.
    check_final_carry_or: assert property (
        @(posedge clk) c_out == (wire_carry0 | wire_carry1)
    );

    // End-to-end sum matches a 3-input XOR.
    check_full_sum_xor: assert property (
        @(posedge clk) s_out == (x_in ^ y_in ^ c_in)
    );

    // End-to-end carry is high when at least two inputs are high.
    check_full_carry_majority: assert property (
        @(posedge clk) c_out == ((x_in & y_in) | (x_in & c_in) | (y_in & c_in))
    );

    // Output pair equals the arithmetic sum of the three 1-bit inputs.
    check_full_adder_arithmetic: assert property (
        @(posedge clk) {c_out, s_out} == ({1'b0, x_in} + {1'b0, y_in} + {1'b0, c_in})
    );

endmodule