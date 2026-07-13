module sparc_ifu_incr46_sva (
    input logic        clk,
    input logic [45:0] a,
    input logic [45:0] a_inc,
    input logic        ofl
);

    // a_inc must always be the 46-bit input incremented by one.
    check_increment_result: assert property (
        @(posedge clk) a_inc == (a + 46'd1)
    );

    // ofl must follow the RTL overflow expression.
    check_overflow_definition: assert property (
        @(posedge clk) ofl == ((~a[45]) & a_inc[45])
    );

    // Overflow occurs only when incrementing the largest positive 46-bit value.
    check_overflow_condition: assert property (
        @(posedge clk) ofl == ((~a[45]) & (&a[44:0]))
    );

    // Zero must increment to one without overflow.
    check_zero_case: assert property (
        @(posedge clk) (a == 46'd0) |-> (a_inc == 46'd1) && (ofl == 1'b0)
    );

    // The largest positive value must roll to the sign bit and assert overflow.
    check_positive_max_case: assert property (
        @(posedge clk) (a == {1'b0, {45{1'b1}}}) |-> (a_inc == {1'b1, {45{1'b0}}}) && (ofl == 1'b1)
    );

    // All ones must wrap to zero without overflow.
    check_all_ones_wrap_case: assert property (
        @(posedge clk) (a == {46{1'b1}}) |-> (a_inc == 46'd0) && (ofl == 1'b0)
    );

endmodule