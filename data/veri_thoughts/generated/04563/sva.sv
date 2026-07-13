module multi_QI_sva (
    input logic        CLK,
    input logic        reset,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [31:0] P
);

    // First clock after a sampled reset still sees P cleared.
    check_post_reset_clears_p: assert property (
        @(posedge CLK) disable iff (reset)
        (!$initstate && $past(reset)) |-> (P == 32'd0)
    );

    // Outside reset, P must be either zero or the previous cycle's product.
    check_p_is_zero_or_prev_product: assert property (
        @(posedge CLK) disable iff (reset)
        (!$initstate) |-> ((P == 32'd0) || (P == ($past(A) * $past(B))))
    );

    // Any nonzero P must come from the previous cycle's multiplication.
    check_nonzero_p_matches_prev_product: assert property (
        @(posedge CLK) disable iff (reset)
        (!$initstate && (P != 32'd0)) |-> (P == ($past(A) * $past(B)))
    );

    // A zero A operand on the previous active cycle forces P to zero.
    check_prev_a_zero_forces_zero: assert property (
        @(posedge CLK) disable iff (reset)
        (!$initstate && !$past(reset) && ($past(A) == 16'd0)) |-> (P == 32'd0)
    );

    // A zero B operand on the previous active cycle forces P to zero.
    check_prev_b_zero_forces_zero: assert property (
        @(posedge CLK) disable iff (reset)
        (!$initstate && !$past(reset) && ($past(B) == 16'd0)) |-> (P == 32'd0)
    );

    // Multiplying by one on A passes through the previous B value unless reset cleared P.
    check_prev_a_one_identity: assert property (
        @(posedge CLK) disable iff (reset)
        (!$initstate && !$past(reset) && ($past(A) == 16'd1)) |-> ((P == 32'd0) || (P == {16'd0, $past(B)}))
    );

    // Multiplying by one on B passes through the previous A value unless reset cleared P.
    check_prev_b_one_identity: assert property (
        @(posedge CLK) disable iff (reset)
        (!$initstate && !$past(reset) && ($past(B) == 16'd1)) |-> ((P == 32'd0) || (P == {16'd0, $past(A)}))
    );

    // If either previous operand was even, the stored result must be even.
    check_even_operand_gives_even_result: assert property (
        @(posedge CLK) disable iff (reset)
        (!$initstate && !$past(reset) && (!$past(A[0]) || !$past(B[0]))) |-> (P[0] == 1'b0)
    );

    // A nonzero result from two odd previous operands must also be odd.
    check_odd_operands_nonzero_result_is_odd: assert property (
        @(posedge CLK) disable iff (reset)
        (!$initstate && !$past(reset) && (P != 32'd0) && $past(A[0]) && $past(B[0])) |-> (P[0] == 1'b1)
    );

    // The maximum 16x16 product is either captured exactly or cleared by reset.
    check_max_operands_product: assert property (
        @(posedge CLK) disable iff (reset)
        (!$initstate && !$past(reset) && ($past(A) == 16'hffff) && ($past(B) == 16'hffff)) |-> ((P == 32'd0) || (P == 32'hfffe_0001))
    );

endmodule