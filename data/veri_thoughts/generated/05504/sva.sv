module shift_adder_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] s,
    input logic overflow,
    input logic [2:0] shift_reg,
    input logic [7:0] a_reg,
    input logic [7:0] b_reg,
    input logic [15:0] product,
    input logic [8:0] sum,
    input logic carry
);

    // a_reg captures a on each clock.
    check_a_reg_captures_a: assert property (
        @(posedge clk) !$initstate |-> (a_reg == $past(a))
    );

    // b_reg captures b on each clock.
    check_b_reg_captures_b: assert property (
        @(posedge clk) !$initstate |-> (b_reg == $past(b))
    );

    // shift_reg shifts left and inserts 0 in bit 0.
    check_shift_reg_shift_behavior: assert property (
        @(posedge clk) !$initstate |-> (shift_reg == {$past(shift_reg[1:0]), 1'b0})
    );

    // shift_reg bit 0 is cleared after the first clock.
    check_shift_reg_lsb_zero: assert property (
        @(posedge clk) !$initstate |-> (shift_reg[0] == 1'b0)
    );

    // product is the multiplication of the registered inputs.
    check_product_definition: assert property (
        @(posedge clk) product == (a_reg * b_reg)
    );

    // sum is product[7:0] plus shift_reg.
    check_sum_definition: assert property (
        @(posedge clk) sum == (product[7:0] + shift_reg)
    );

    // carry is product[8] OR sum[8].
    check_carry_definition: assert property (
        @(posedge clk) carry == (product[8] | sum[8])
    );

    // s is the low byte of sum.
    check_s_matches_sum_low_byte: assert property (
        @(posedge clk) s == sum[7:0]
    );

    // overflow mirrors carry.
    check_overflow_matches_carry: assert property (
        @(posedge clk) overflow == carry
    );

    // overflow matches the implemented carry expression.
    check_overflow_matches_expression: assert property (
        @(posedge clk) overflow == (product[8] | sum[8])
    );

endmodule