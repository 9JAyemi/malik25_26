module ripple_shift_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic carry_in,
    input logic select,
    input logic [3:0] out,
    input logic carry_out
);

    // Add mode returns the full 5-bit A+B+carry_in result.
    check_add_path_full_result: assert property (
        @(posedge clk)
        (!select) |-> ({carry_out, out} == ({1'b0, A} + {1'b0, B} + {{4{1'b0}}, carry_in}))
    );

    // Shift mode returns A left-shifted by B.
    check_shift_path_output: assert property (
        @(posedge clk)
        select |-> (out == (A << B))
    );

    // carry_out always matches the adder carry bit.
    check_carry_out_matches_adder: assert property (
        @(posedge clk)
        (carry_out == (({1'b0, A} + {1'b0, B} + {{4{1'b0}}, carry_in}) >= 5'd16))
    );

    // In add mode, bit 0 follows the full-adder XOR equation.
    check_add_lsb_sum: assert property (
        @(posedge clk)
        (!select) |-> (out[0] == (A[0] ^ B[0] ^ carry_in))
    );

    // A zero shift amount passes A through in shift mode.
    check_shift_zero_amount_passes_a: assert property (
        @(posedge clk)
        (select && (B == 4'h0)) |-> (out == A)
    );

    // Shifting a 4-bit value by 4 or more clears the output.
    check_shift_large_amount_clears_out: assert property (
        @(posedge clk)
        (select && (B >= 4'd4)) |-> (out == 4'h0)
    );

    // A zero input stays zero in shift mode.
    check_shift_zero_input_yields_zero: assert property (
        @(posedge clk)
        (select && (A == 4'h0)) |-> (out == 4'h0)
    );

    // Zero operands in add mode only reflect carry_in.
    check_add_zero_operands_reflect_carry_in: assert property (
        @(posedge clk)
        ((!select) && (A == 4'h0) && (B == 4'h0)) |-> ((out == {3'b000, carry_in}) && (carry_out == 1'b0))
    );

    // Zero B and zero carry pass A through in add mode.
    check_add_zero_b_no_carry_passes_a: assert property (
        @(posedge clk)
        ((!select) && (B == 4'h0) && (carry_in == 1'b0)) |-> ((out == A) && (carry_out == 1'b0))
    );

    // Zero A and zero carry pass B through in add mode.
    check_add_zero_a_no_carry_passes_b: assert property (
        @(posedge clk)
        ((!select) && (A == 4'h0) && (carry_in == 1'b0)) |-> ((out == B) && (carry_out == 1'b0))
    );

endmodule