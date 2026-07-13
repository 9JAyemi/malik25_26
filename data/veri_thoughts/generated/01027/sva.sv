module two_bit_comparator_sva (
    input logic clk,
    input logic [1:0] a,
    input logic [1:0] b,
    input logic out
);
    ///// Functional equivalence /////
    // out equals AND of the OR-reductions of a and b.
    check_out_eq_and_of_ors: assert property (
        @(posedge clk) disable iff (1'b0) out == ((a[1] | a[0]) & (b[1] | b[0]))
    );
    // out equals the sum-of-products of all a/b bit pairs.
    check_out_eq_sum_of_products: assert property (
        @(posedge clk) disable iff (1'b0) out == ((a[1] & b[1]) | (a[1] & b[0]) | (a[0] & b[1]) | (a[0] & b[0]))
    );

    ///// Necessary conditions /////
    // If a is zero, out must be zero.
    check_a_zero_forces_out0: assert property (
        @(posedge clk) disable iff (1'b0) (a == 2'b00) |-> (out == 1'b0)
    );
    // If b is zero, out must be zero.
    check_b_zero_forces_out0: assert property (
        @(posedge clk) disable iff (1'b0) (b == 2'b00) |-> (out == 1'b0)
    );
    // If out is one, both a and b must be non-zero.
    check_out1_implies_nonzero_inputs: assert property (
        @(posedge clk) disable iff (1'b0) (out == 1'b1) |-> ((a != 2'b00) && (b != 2'b00))
    );
    // If out is zero, at least one of a or b must be zero.
    check_out0_implies_one_zero: assert property (
        @(posedge clk) disable iff (1'b0) (out == 1'b0) |-> ((a == 2'b00) || (b == 2'b00))
    );

    ///// Sufficient conditions /////
    // If both a and b are non-zero, out must be one.
    check_nonzero_inputs_force_out1: assert property (
        @(posedge clk) disable iff (1'b0) ((a != 2'b00) && (b != 2'b00)) |-> (out == 1'b1)
    );
    // If exactly one of a or b is zero, out must be zero.
    check_exactly_one_zero_forces_out0: assert property (
        @(posedge clk) disable iff (1'b0) (((a == 2'b00) ^ (b == 2'b00))) |-> (out == 1'b0)
    );
endmodule