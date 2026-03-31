module sky130_fd_sc_ls__ha_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B
);

// SUM is the XOR of A and B.
    check_sum_xor: assert property (
        @(posedge clk) SUM == (A ^ B)
    );

// COUT is the AND of A and B.
    check_cout_and: assert property (
        @(posedge clk) COUT == (A & B)
    );

// When A and B are equal, SUM must be 0.
    check_sum_zero_when_equal: assert property (
        @(posedge clk) (A == B) |-> (SUM == 1'b0)
    );

// When A and B differ, SUM must be 1.
    check_sum_one_when_different: assert property (
        @(posedge clk) (A != B) |-> (SUM == 1'b1)
    );

// When A is 0, SUM must equal B.
    check_sum_equals_b_when_a0: assert property (
        @(posedge clk) (A == 1'b0) |-> (SUM == B)
    );

// When A is 1, SUM must be the inverse of B.
    check_sum_inverts_b_when_a1: assert property (
        @(posedge clk) (A == 1'b1) |-> (SUM == ~B)
    );

// When B is 0, SUM must equal A.
    check_sum_equals_a_when_b0: assert property (
        @(posedge clk) (B == 1'b0) |-> (SUM == A)
    );

// When B is 1, SUM must be the inverse of A.
    check_sum_inverts_a_when_b1: assert property (
        @(posedge clk) (B == 1'b1) |-> (SUM == ~A)
    );

// When both inputs are 0, COUT must be 0.
    check_cout_zero_when_both_zero: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b0)) |-> (COUT == 1'b0)
    );

// When both inputs are 1, COUT must be 1.
    check_cout_one_when_both_one: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b1)) |-> (COUT == 1'b1)
    );

// When A is 0, COUT must be 0.
    check_cout_zero_when_a0: assert property (
        @(posedge clk) (A == 1'b0) |-> (COUT == 1'b0)
    );

// When A is 1, COUT must equal B.
    check_cout_equals_b_when_a1: assert property (
        @(posedge clk) (A == 1'b1) |-> (COUT == B)
    );

// When B is 0, COUT must be 0.
    check_cout_zero_when_b0: assert property (
        @(posedge clk) (B == 1'b0) |-> (COUT == 1'b0)
    );

// When B is 1, COUT must equal A.
    check_cout_equals_a_when_b1: assert property (
        @(posedge clk) (B == 1'b1) |-> (COUT == A)
    );

endmodule
