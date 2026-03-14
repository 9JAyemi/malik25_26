module top_module_sva (
    input logic clk,
    input logic signed [31:0] a,
    input logic signed [31:0] b,
    input logic [7:0] input1,
    input logic [7:0] input2,
    input logic control,
    input logic [1:0] result,
    input logic signed [31:0] sum
);
    // Helper expressions for readability
    let and_two_bits = ( (input1[0] & input2[0]) & (input1[1] & input2[1]) );
    let or_lsb       = ( input1[0] | input2[0] );
    let prod16       = ( $signed(input1) * $signed(input2) );              // 16-bit signed
    let zext_prod32  = {16'd0, prod16[15:0]};                              // zero-extend to 32

    ///// result_reg behavior /////
    // result[0] is always driven LOW by the sequential logic.
    check_result_lsb_zero: assert property (
        @(posedge clk) result[0] == 1'b0
    );

    // When previous control was 0, result[1] equals previous AND of selected input bits.
    check_result_sel0_msb: assert property (
        @(posedge clk) ($past(control) == 1'b0) |-> (result[1] == $past(and_two_bits))
    );

    // When previous control was 0, full result vector matches {AND,0}.
    check_result_sel0_full: assert property (
        @(posedge clk) ($past(control) == 1'b0) |-> (result == {$past(and_two_bits), 1'b0})
    );

    // When previous control was 1, result[1] equals the OR(LSB) from two cycles ago (due to extra register).
    check_result_sel1_msb: assert property (
        @(posedge clk) ($past(control) == 1'b1) |-> (result[1] == $past($past(or_lsb)))
    );

    // When previous control was 1, full result vector matches {OR(LSB from two cycles ago),0}.
    check_result_sel1_full: assert property (
        @(posedge clk) ($past(control) == 1'b1) |-> (result == {$past($past(or_lsb)), 1'b0})
    );

    ///// sum_reg behavior /////
    // sum equals a + b + zero-extended 16-bit signed product of input1*input2 from previous cycle.
    check_sum_update: assert property (
        @(posedge clk) sum == $past(a + b + zext_prod32)
    );

    // The contribution (sum - a - b) equals the zero-extended product from previous cycle.
    check_sum_contribution_exact: assert property (
        @(posedge clk) (sum - $past(a) - $past(b)) == $past(zext_prod32)
    );

    // The upper 16 bits of (sum - a - b) are always zero (due to zero-extension).
    check_sum_contribution_upper_zero: assert property (
        @(posedge clk) (sum - $past(a) - $past(b))[31:16] == 16'h0000
    );

    // The lower 16 bits of (sum - a - b) equal the product's lower 16 bits from previous cycle.
    check_sum_contribution_lower_match: assert property (
        @(posedge clk) (sum - $past(a) - $past(b))[15:0] == $past(prod16[15:0])
    );

endmodule