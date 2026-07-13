module sky130_fd_sc_hdll__nand4bb_sva (
    input logic Y,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D
);
    // Analysis: no clock/reset; pure combinational; Y = A_N | B_N | ~(C & D).
    // All assertions sample on posedge of any input signal.

    // Y must equal the combinational function (case-equality tolerates X/Z).
    check_functional_equivalence: assert property (
        @(posedge A_N or posedge B_N or posedge C or posedge D)
            (Y === (A_N | B_N | ~(C & D)))
    );

    // Known inputs produce known Y.
    check_known_inputs_imply_known_Y: assert property (
        @(posedge A_N or posedge B_N or posedge C or posedge D)
            (!$isunknown({A_N, B_N, C, D})) |-> (!$isunknown(Y))
    );

    // If A_N is HIGH, Y must be HIGH.
    check_A_N_high_implies_Y_high: assert property (
        @(posedge A_N or posedge B_N or posedge C or posedge D)
            (A_N == 1'b1) |-> (Y == 1'b1)
    );

    // If B_N is HIGH, Y must be HIGH.
    check_B_N_high_implies_Y_high: assert property (
        @(posedge A_N or posedge B_N or posedge C or posedge D)
            (B_N == 1'b1) |-> (Y == 1'b1)
    );

    // If C is LOW, Y must be HIGH.
    check_C_low_implies_Y_high: assert property (
        @(posedge A_N or posedge B_N or posedge C or posedge D)
            (C == 1'b0) |-> (Y == 1'b1)
    );

    // If D is LOW, Y must be HIGH.
    check_D_low_implies_Y_high: assert property (
        @(posedge A_N or posedge B_N or posedge C or posedge D)
            (D == 1'b0) |-> (Y == 1'b1)
    );

    // When C and D are HIGH, Y reduces to A_N | B_N.
    check_reduce_when_C_D_high: assert property (
        @(posedge A_N or posedge B_N or posedge C or posedge D)
            (C && D) |-> (Y === (A_N | B_N))
    );

    // When A_N and B_N are LOW, Y reduces to ~(C & D).
    check_reduce_when_A_B_low: assert property (
        @(posedge A_N or posedge B_N or posedge C or posedge D)
            (!A_N && !B_N) |-> (Y === ~(C & D))
    );

    // If A_N and B_N are LOW and C and D are HIGH, Y must be LOW.
    check_all_force_low_implies_Y_low: assert property (
        @(posedge A_N or posedge B_N or posedge C or posedge D)
            (!A_N && !B_N && C && D) |-> (Y == 1'b0)
    );

    // If Y is LOW, then A_N=0, B_N=0, C=1, D=1.
    check_Y_low_requires_inputs: assert property (
        @(posedge A_N or posedge B_N or posedge C or posedge D)
            (Y == 1'b0) |-> (!A_N && !B_N && C && D)
    );

endmodule