module sky130_fd_sc_hdll__xor2b_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic X
);
    // X matches the RTL equation: C ? (A^B) : (A|B)
    check_function_equation: assert property (
        @(posedge clk) X == (C ? (A ^ B) : (A | B))
    );

    // When C is 1, X is A xor B
    check_select_high_is_xor: assert property (
        @(posedge clk) (C == 1'b1) |-> (X == (A ^ B))
    );

    // When C is 0, X is A or B
    check_select_low_is_or: assert property (
        @(posedge clk) (C == 1'b0) |-> (X == (A | B))
    );

    // With C=0 and A==B, X equals A
    check_c_low_equal_inputs_pass_through: assert property (
        @(posedge clk) (C == 1'b0) && (A == B) |-> (X == A)
    );

    // If A=0 and B=0, X must be 0
    check_both_zero_results_zero: assert property (
        @(posedge clk) (A == 1'b0) && (B == 1'b0) |-> (X == 1'b0)
    );

    // If A=1, B=1, and C=1, then X must be 0
    check_both_one_c_high_results_zero: assert property (
        @(posedge clk) (A == 1'b1) && (B == 1'b1) && (C == 1'b1) |-> (X == 1'b0)
    );

    // If A=1, B=1, and C=0, then X must be 1
    check_both_one_c_low_results_one: assert property (
        @(posedge clk) (A == 1'b1) && (B == 1'b1) && (C == 1'b0) |-> (X == 1'b1)
    );

    // With C=1, differing inputs imply X=1
    check_c_high_inputs_differ_results_one: assert property (
        @(posedge clk) (C == 1'b1) && (A != B) |-> (X == 1'b1)
    );

    // With C=1, equal inputs imply X=0
    check_c_high_inputs_equal_results_zero: assert property (
        @(posedge clk) (C == 1'b1) && (A == B) |-> (X == 1'b0)
    );

    // With C=0, any input high implies X=1
    check_c_low_any_one_results_one: assert property (
        @(posedge clk) (C == 1'b0) && ((A == 1'b1) || (B == 1'b1)) |-> (X == 1'b1)
    );
endmodule