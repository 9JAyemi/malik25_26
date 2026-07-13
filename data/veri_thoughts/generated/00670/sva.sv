module adder4_sva (
    input  logic        clk,  // Sampling clock for assertions (DUT has no clock/reset)
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic [3:0]  S
);
    ///// Functional correctness /////
    // S equals A + B modulo 16 (matches combinational RTL behavior).
    check_sum_mod16: assert property (
        @(posedge clk) S == (A + B)
    );

    ///// Combinational behavior /////
    // If A and B are stable, S must be stable.
    check_stable_on_stable_inputs: assert property (
        @(posedge clk) $stable(A) && $stable(B) |-> $stable(S)
    );
    // S only changes if A or B changes.
    check_output_changes_only_on_input_change: assert property (
        @(posedge clk) $changed(S) |-> ($changed(A) || $changed(B))
    );

    ///// Identities /////
    // Adding zero on A leaves S equal to B.
    check_add_identity_A_zero: assert property (
        @(posedge clk) (A == 4'h0) |-> (S == B)
    );
    // Adding zero on B leaves S equal to A.
    check_add_identity_B_zero: assert property (
        @(posedge clk) (B == 4'h0) |-> (S == A)
    );
    // Zero plus zero yields zero.
    check_add_zero_zero: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0) |-> (S == 4'h0)
    );

    ///// Wrap-around examples (mod-16) /////
    // 15 + 1 wraps to 0.
    check_wrap_F_plus_1_A: assert property (
        @(posedge clk) (A == 4'hF && B == 4'h1) |-> (S == 4'h0)
    );
    // 1 + 15 wraps to 0.
    check_wrap_1_plus_F_B: assert property (
        @(posedge clk) (A == 4'h1 && B == 4'hF) |-> (S == 4'h0)
    );
    // 15 + 15 yields 14 (mod 16).
    check_15_plus_15: assert property (
        @(posedge clk) (A == 4'hF && B == 4'hF) |-> (S == 4'hE)
    );

    ///// Commutativity across cycles /////
    // Swapping A and B across cycles leaves S unchanged.
    check_commutativity_across_swap: assert property (
        @(posedge clk) (A == $past(B) && B == $past(A)) |-> (S == $past(S))
    );
endmodule