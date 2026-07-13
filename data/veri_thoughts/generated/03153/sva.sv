module ripple_carry_adder_4bit_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);

    // Full 5-bit result must equal a + b + cin.
    check_full_result_matches_addition: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // Bit 0 sum must match the 1-bit full-adder XOR equation.
    check_lsb_sum_matches_full_adder: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Bit 1 sum must use the carry generated from bit 0.
    check_bit1_sum_uses_bit0_carry: assert property (
        @(posedge clk) sum[1] == (a[1] ^ b[1] ^ ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin)))
    );

    // Carry-out must indicate overflow of the 4-bit addition.
    check_cout_matches_overflow: assert property (
        @(posedge clk) cout == (({1'b0, a} + {1'b0, b} + cin) >= 5'd16)
    );

    // Zero inputs must produce a zero result.
    check_zero_inputs_return_zero: assert property (
        @(posedge clk) ((a == 4'b0000) && (b == 4'b0000) && (cin == 1'b0)) |-> ((sum == 4'b0000) && (cout == 1'b0))
    );

    // Adding zero with no carry-in must pass a through unchanged.
    check_a_passthrough_when_b_and_cin_are_zero: assert property (
        @(posedge clk) ((b == 4'b0000) && (cin == 1'b0)) |-> ((sum == a) && (cout == 1'b0))
    );

    // Adding zero with no carry-in must pass b through unchanged.
    check_b_passthrough_when_a_and_cin_are_zero: assert property (
        @(posedge clk) ((a == 4'b0000) && (cin == 1'b0)) |-> ((sum == b) && (cout == 1'b0))
    );

    // Maximum inputs must produce all ones with carry-out asserted.
    check_max_input_case: assert property (
        @(posedge clk) ((a == 4'b1111) && (b == 4'b1111) && (cin == 1'b1)) |-> ((sum == 4'b1111) && (cout == 1'b1))
    );

endmodule