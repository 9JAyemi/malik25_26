module my_or2_8_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

// X matches the RTL expression C ? ~or(A,B) : or(A,B).
    check_function_equivalence: assert property (
        @(posedge clk) X == (C ? ~((A | B)) : (A | B))
    );

// When C is 0, X equals A | B.
    check_c0_pass_through: assert property (
        @(posedge clk) (C == 1'b0) |-> (X == (A | B))
    );

// When C is 1, X equals ~(A | B).
    check_c1_invert: assert property (
        @(posedge clk) (C == 1'b1) |-> (X == ~(A | B))
    );

// If both A and B are 0, X must be 0.
    check_both_zero: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b0)) |-> (X == 1'b0)
    );

// If A is 1, X must be 1.
    check_a_one: assert property (
        @(posedge clk) (A == 1'b1) |-> (X == 1'b1)
    );

// If B is 1, X must be 1.
    check_b_one: assert property (
        @(posedge clk) (B == 1'b1) |-> (X == 1'b1)
    );

// If C is 1 and A and B are 0, X must be 1.
    check_c1_both_zero: assert property (
        @(posedge clk) ((C == 1'b1) && (A == 1'b0) && (B == 1'b0)) |-> (X == 1'b1)
    );

// If C is 0 and A or B is 0, X must be 0.
    check_c0_one_zero: assert property (
        @(posedge clk) ((C == 1'b0) && ((A == 1'b0) || (B == 1'b0))) |-> (X == 1'b0)
    );

endmodule
