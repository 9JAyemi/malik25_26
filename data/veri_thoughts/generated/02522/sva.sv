module sky130_fd_sc_hs__and2_1_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic VPWR,
    input logic VGND
);
    // X equals ~(A & B).
    check_and2_1_func_is_nand: assert property (
        @($global_clock) X == ~(A & B)
    );
    // If both A and B are 1, X must be 0.
    check_and2_1_A1B1_forces_X0: assert property (
        @($global_clock) (A && B) |-> (X == 1'b0)
    );
    // If A is 0, X must be 1.
    check_and2_1_A0_forces_X1: assert property (
        @($global_clock) (!A) |-> (X == 1'b1)
    );
    // If B is 0, X must be 1.
    check_and2_1_B0_forces_X1: assert property (
        @($global_clock) (!B) |-> (X == 1'b1)
    );
    // If X is 1, at least one input is 0.
    check_and2_1_X1_implies_A0_or_B0: assert property (
        @($global_clock) X |-> (!A || !B)
    );
endmodule

module sky130_fd_sc_hs__and2_1_comb_sva (
    input logic X,
    input logic A,
    input logic B
);
    // X equals (A & B).
    check_and2_1_comb_func_is_and: assert property (
        @($global_clock) X == (A & B)
    );
    // If A is 0, X must be 0.
    check_and2_1_comb_A0_forces_X0: assert property (
        @($global_clock) (!A) |-> (X == 1'b0)
    );
    // If B is 0, X must be 0.
    check_and2_1_comb_B0_forces_X0: assert property (
        @($global_clock) (!B) |-> (X == 1'b0)
    );
    // If X is 1, both inputs are 1.
    check_and2_1_comb_X1_implies_A1_and_B1: assert property (
        @($global_clock) X |-> (A && B)
    );
    // If both A and B are 1, X must be 1.
    check_and2_1_comb_A1B1_forces_X1: assert property (
        @($global_clock) (A && B) |-> (X == 1'b1)
    );
endmodule

module sky130_fd_sc_hs__nand2_1_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic VPWR,
    input logic VGND
);
    // Y equals (~A & ~B).
    check_nand2_1_func_is_nor: assert property (
        @($global_clock) Y == ((~A) & (~B))
    );
    // If A is 1, Y must be 0.
    check_nand2_1_A1_forces_Y0: assert property (
        @($global_clock) A |-> (Y == 1'b0)
    );
    // If B is 1, Y must be 0.
    check_nand2_1_B1_forces_Y0: assert property (
        @($global_clock) B |-> (Y == 1'b0)
    );
    // If both A and B are 0, Y must be 1.
    check_nand2_1_A0B0_forces_Y1: assert property (
        @($global_clock) (!A && !B) |-> (Y == 1'b1)
    );
    // If Y is 1, both inputs are 0.
    check_nand2_1_Y1_implies_A0_and_B0: assert property (
        @($global_clock) Y |-> (!A && !B)
    );
endmodule

module sky130_fd_sc_hs__nand2_1_comb_sva (
    input logic Y,
    input logic A,
    input logic B
);
    // Y equals ~(A & B).
    check_nand2_1_comb_func_is_nand: assert property (
        @($global_clock) Y == ~(A & B)
    );
    // If both A and B are 1, Y must be 0.
    check_nand2_1_comb_A1B1_forces_Y0: assert property (
        @($global_clock) (A && B) |-> (Y == 1'b0)
    );
    // If A is 0, Y must be 1.
    check_nand2_1_comb_A0_forces_Y1: assert property (
        @($global_clock) (!A) |-> (Y == 1'b1)
    );
    // If B is 0, Y must be 1.
    check_nand2_1_comb_B0_forces_Y1: assert property (
        @($global_clock) (!B) |-> (Y == 1'b1)
    );
    // If Y is 1, at least one input is 0.
    check_nand2_1_comb_Y1_implies_A0_or_B0: assert property (
        @($global_clock) Y |-> (!A || !B)
    );
endmodule

module sky130_fd_sc_hs__and3b_1_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND
);
    // X equals ~(A & B & C).
    check_and3b_1_func_is_nand3: assert property (
        @($global_clock) X == ~(A & B & C)
    );
    // If all A,B,C are 1, X must be 0.
    check_and3b_1_all1_forces_X0: assert property (
        @($global_clock) (A && B && C) |-> (X == 1'b0)
    );
    // If A is 0, X must be 1.
    check_and3b_1_A0_forces_X1: assert property (
        @($global_clock) (!A) |-> (X == 1'b1)
    );
    // If B is 0, X must be 1.
    check_and3b_1_B0_forces_X1: assert property (
        @($global_clock) (!B) |-> (X == 1'b1)
    );
    // If C is 0, X must be 1.
    check_and3b_1_C0_forces_X1: assert property (
        @($global_clock) (!C) |-> (X == 1'b1)
    );
    // If X is 0, all inputs are 1.
    check_and3b_1_X0_implies_all1: assert property (
        @($global_clock) (X == 1'b0) |-> (A && B && C)
    );
endmodule