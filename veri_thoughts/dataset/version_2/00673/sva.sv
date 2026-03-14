module mux_sva (
    input logic clk,       // verification clock (RTL has no clock/reset)
    input logic A,
    input logic B,
    input logic C,
    input logic invert,
    input logic out
);
    // Functional equivalence: out matches the mux/invert expression
    check_functional_equiv: assert property (
        @(posedge clk) out == (C ? (invert ? ~B : B) : A)
    );

    // When C==0, out equals A
    check_sel_C0: assert property (
        @(posedge clk) (C == 1'b0) |-> (out == A)
    );

    // When C==1 and invert==0, out equals B
    check_sel_C1_inv0: assert property (
        @(posedge clk) ((C == 1'b1) && (invert == 1'b0)) |-> (out == B)
    );

    // When C==1 and invert==1, out equals ~B
    check_sel_C1_inv1: assert property (
        @(posedge clk) ((C == 1'b1) && (invert == 1'b1)) |-> (out == ~B)
    );

    // When C==1, out equals B XOR invert
    check_C1_xor: assert property (
        @(posedge clk) (C == 1'b1) |-> (out == (B ^ invert))
    );

    // On C rising, out follows the B/invert path
    check_rose_C: assert property (
        @(posedge clk) $rose(C) |-> (out == (invert ? ~B : B))
    );

    // On C falling, out follows A
    check_fell_C: assert property (
        @(posedge clk) $fell(C) |-> (out == A)
    );

    // On invert rising while C==1, out becomes ~B
    check_rose_invert_C1: assert property (
        @(posedge clk) (C == 1'b1) && $rose(invert) |-> (out == ~B)
    );

    // On invert falling while C==1, out becomes B
    check_fell_invert_C1: assert property (
        @(posedge clk) (C == 1'b1) && $fell(invert) |-> (out == B)
    );

    // When B changes and C==1, out updates per invert
    check_B_change_C1: assert property (
        @(posedge clk) (C == 1'b1) && $changed(B) |-> (out == (invert ? ~B : B))
    );

    // When A changes and C==0, out updates to A
    check_A_change_C0: assert property (
        @(posedge clk) (C == 1'b0) && $changed(A) |-> (out == A)
    );

    // If all inputs are stable, out remains stable
    check_stable_inputs_imply_stable_out: assert property (
        @(posedge clk) $stable(A) && $stable(B) && $stable(C) && $stable(invert) |-> $stable(out)
    );
endmodule