module sky130_fd_sc_ls__nor4bb_sva (
    input  logic Y,
    input  logic A,
    input  logic B,
    input  logic C_N,
    input  logic D_N,
    input  logic VPWR,
    input  logic VGND,
    input  logic VPB,
    input  logic VNB
);
    // Y equals NOR of A,B, C_N, D_N when A rises.
    check_y_eq_nor_on_A: assert property (
        @(posedge A) Y == ~(A | B | C_N | D_N)
    );

    // Y equals NOR of A,B, C_N, D_N when B rises.
    check_y_eq_nor_on_B: assert property (
        @(posedge B) Y == ~(A | B | C_N | D_N)
    );

    // Y equals NOR of A,B, C_N, D_N when C_N rises.
    check_y_eq_nor_on_C_N: assert property (
        @(posedge C_N) Y == ~(A | B | C_N | D_N)
    );

    // Y equals NOR of A,B, C_N, D_N when D_N rises.
    check_y_eq_nor_on_D_N: assert property (
        @(posedge D_N) Y == ~(A | B | C_N | D_N)
    );

    // If Y rises HIGH, then all inputs must be LOW at that time.
    check_y_high_implies_all_low: assert property (
        @(posedge Y) (A == 1'b0) && (B == 1'b0) && (C_N == 1'b0) && (D_N == 1'b0)
    );

    // If Y falls LOW, at least one input must be HIGH at that time.
    check_y_low_implies_some_high: assert property (
        @(negedge Y) (A == 1'b1) || (B == 1'b1) || (C_N == 1'b1) || (D_N == 1'b1)
    );
endmodule