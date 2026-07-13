module sky130_fd_sc_ms__nand4bb_sva (
    input logic CLK,
    input logic Y,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D
);
    // Y equals the combinational function A_N | B_N | ~(C & D).
    check_functional_equivalence: assert property (
        @(posedge CLK) Y == (A_N | B_N | ~(C & D))
    );

    // If Y is LOW, then A_N=0, B_N=0, and C&D=1 must hold.
    check_y_low_conditions: assert property (
        @(posedge CLK) (Y == 1'b0) |-> ((A_N == 1'b0) && (B_N == 1'b0) && (C == 1'b1) && (D == 1'b1))
    );

    // A_N HIGH forces Y HIGH.
    check_a_n_dominates: assert property (
        @(posedge CLK) (A_N == 1'b1) |-> (Y == 1'b1)
    );

    // B_N HIGH forces Y HIGH.
    check_b_n_dominates: assert property (
        @(posedge CLK) (B_N == 1'b1) |-> (Y == 1'b1)
    );

    // C LOW forces Y HIGH (since ~(C&D)=1).
    check_c_low_forces_y_high: assert property (
        @(posedge CLK) (C == 1'b0) |-> (Y == 1'b1)
    );

    // D LOW forces Y HIGH (since ~(C&D)=1).
    check_d_low_forces_y_high: assert property (
        @(posedge CLK) (D == 1'b0) |-> (Y == 1'b1)
    );

    // With A_N=0 and B_N=0, Y reduces to ~(C & D).
    check_reduce_when_an_bn_low: assert property (
        @(posedge CLK) ((A_N == 1'b0) && (B_N == 1'b0)) |-> (Y == ~(C & D))
    );

    // With C=1 and D=1, Y reduces to A_N | B_N.
    check_reduce_when_c_d_high: assert property (
        @(posedge CLK) ((C == 1'b1) && (D == 1'b1)) |-> (Y == (A_N | B_N))
    );
endmodule