module add8_sva (
    input logic CLK,
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic [7:0] out_sum,
    input logic out_carry
);
    // Sum and carry match implemented 8-bit add with zero-extended carry.
    check_concat_sum_matches_8b_add: assert property (
        @(posedge CLK) {out_carry, out_sum} == {1'b0, (in_a + in_b)}
    );

    // out_sum equals 8-bit addition of inputs.
    check_sum_matches_8b_add: assert property (
        @(posedge CLK) out_sum == (in_a + in_b)
    );

    // out_carry is always zero due to zero-extension of 8-bit result.
    check_carry_const_zero: assert property (
        @(posedge CLK) out_carry == 1'b0
    );

    // Adding zero on B leaves A unchanged and carry zero.
    check_zero_b_identity: assert property (
        @(posedge CLK) (in_b == 8'h00) |-> (out_sum == in_a) && (out_carry == 1'b0)
    );

    // Adding zero on A leaves B unchanged and carry zero.
    check_zero_a_identity: assert property (
        @(posedge CLK) (in_a == 8'h00) |-> (out_sum == in_b) && (out_carry == 1'b0)
    );

    // Adding 0xFF on B decrements A modulo 256; carry remains zero.
    check_ff_b_decrement: assert property (
        @(posedge CLK) (in_b == 8'hFF) |-> (out_sum == (in_a - 8'h01)) && (out_carry == 1'b0)
    );

    // Adding 0xFF on A decrements B modulo 256; carry remains zero.
    check_ff_a_decrement: assert property (
        @(posedge CLK) (in_a == 8'hFF) |-> (out_sum == (in_b - 8'h01)) && (out_carry == 1'b0)
    );

    // Both inputs zero produce zero sum and zero carry.
    check_both_zero_result_zero: assert property (
        @(posedge CLK) (in_a == 8'h00 && in_b == 8'h00) |-> (out_sum == 8'h00) && (out_carry == 1'b0)
    );

    // Both inputs 0xFF produce 0xFE sum and zero carry (8-bit addition).
    check_both_ff_result_fe: assert property (
        @(posedge CLK) (in_a == 8'hFF && in_b == 8'hFF) |-> (out_sum == 8'hFE) && (out_carry == 1'b0)
    );
endmodule