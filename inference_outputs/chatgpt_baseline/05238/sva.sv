module my_or2_8_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // No RTL clock or reset; sample this combinational logic on the formal global clock.
    // Functional behavior is X = C ? ~(A | B) : (A | B).

    // X must match the RTL conditional assignment.
    check_full_conditional_function: assert property (
        @($global_clock) X == (C ? ~(A | B) : (A | B))
    );

    // When C is low, X must equal A OR B.
    check_c_low_passes_or: assert property (
        @($global_clock) (C == 1'b0) |-> (X == (A | B))
    );

    // When C is high, X must equal the inverse of A OR B.
    check_c_high_inverts_or: assert property (
        @($global_clock) (C == 1'b1) |-> (X == ~(A | B))
    );

    // When both A and B are low, X must follow C.
    check_zero_or_makes_x_follow_c: assert property (
        @($global_clock) ((A == 1'b0) && (B == 1'b0)) |-> (X == C)
    );

    // When either A or B is high, X must invert C.
    check_one_or_makes_x_invert_c: assert property (
        @($global_clock) ((A == 1'b1) || (B == 1'b1)) |-> (X == ~C)
    );

endmodule