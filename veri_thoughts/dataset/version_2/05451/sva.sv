module Test_sva (
    input logic clk,
    input logic [7:0] operand_a,
    input logic [7:0] operand_b,
    input logic [6:0] out
);

    // clk is the only clock; the RTL has no reset.
    // out is the registered low 7 bits of operand_a + operand_b.

    // out captures the lower 7 bits of the previous cycle sum.
    check_registered_truncated_sum: assert property (
        @(posedge clk) 1'b1 |=> ({1'b0, out} == (($past(operand_a) + $past(operand_b)) & 8'h7f))
    );

    // Zero plus zero produces zero on the next cycle.
    check_zero_plus_zero: assert property (
        @(posedge clk) (operand_a == 8'h00 && operand_b == 8'h00) |=> (out == 7'h00)
    );

    // A zero operand_a passes operand_b's low 7 bits to out on the next cycle.
    check_zero_a_passthrough: assert property (
        @(posedge clk) (operand_a == 8'h00) |=> ({1'b0, out} == ($past(operand_b) & 8'h7f))
    );

    // A zero operand_b passes operand_a's low 7 bits to out on the next cycle.
    check_zero_b_passthrough: assert property (
        @(posedge clk) (operand_b == 8'h00) |=> ({1'b0, out} == ($past(operand_a) & 8'h7f))
    );

    // Stable inputs across cycles keep the registered output stable on the following cycle.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) ($stable(operand_a) && $stable(operand_b)) |=> $stable(out)
    );

    // out[0] is the XOR of the previous cycle operand LSBs.
    check_lsb_xor: assert property (
        @(posedge clk) 1'b1 |=> (out[0] == ($past(operand_a[0]) ^ $past(operand_b[0])))
    );

    // When the previous 8-bit sum has bit 7 clear, out matches that full 8-bit sum.
    check_sum_without_bit7_matches_out: assert property (
        @(posedge clk) (((operand_a + operand_b) & 8'h80) == 8'h00) |=> ({1'b0, out} == ($past(operand_a) + $past(operand_b)))
    );

    // When the previous 8-bit sum has bit 7 set, out drops that bit on the next cycle.
    check_sum_with_bit7_drops_msb: assert property (
        @(posedge clk) (((operand_a + operand_b) & 8'h80) == 8'h80) |=> ({1'b0, out} == (($past(operand_a) + $past(operand_b)) - 8'h80))
    );

endmodule