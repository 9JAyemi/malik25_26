module bitwise_and_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] result
);

// Result equals bitwise AND of inputs.
    check_result_matches_and: assert property (
        @(posedge clk) result == (a & b)
    );

// Bit 0 equals a[0] & b[0].
    check_bit0_matches_and: assert property (
        @(posedge clk) result[0] == (a[0] & b[0])
    );

// Bit 1 equals a[1] & b[1].
    check_bit1_matches_and: assert property (
        @(posedge clk) result[1] == (a[1] & b[1])
    );

// Bit 2 equals a[2] & b[2].
    check_bit2_matches_and: assert property (
        @(posedge clk) result[2] == (a[2] & b[2])
    );

// Bit 3 equals a[3] & b[3].
    check_bit3_matches_and: assert property (
        @(posedge clk) result[3] == (a[3] & b[3])
    );

// If a is all zeros, result must be all zeros.
    check_zero_a_implies_zero_result: assert property (
        @(posedge clk) (a == 4'b0000) |-> (result == 4'b0000)
    );

// If b is all zeros, result must be all zeros.
    check_zero_b_implies_zero_result: assert property (
        @(posedge clk) (b == 4'b0000) |-> (result == 4'b0000)
    );

// If a is all ones, result equals b.
    check_ones_a_implies_result_eq_b: assert property (
        @(posedge clk) (a == 4'b1111) |-> (result == b)
    );

// If b is all ones, result equals a.
    check_ones_b_implies_result_eq_a: assert property (
        @(posedge clk) (b == 4'b1111) |-> (result == a)
    );

// If a equals b, result equals a.
    check_equal_inputs_implies_result_eq_a: assert property (
        @(posedge clk) (a == b) |-> (result == a)
    );

endmodule
