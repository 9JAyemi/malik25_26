module sky130_fd_sc_ms__nor4bb_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N
);
    // Combinational gate with no clock/reset; sample on any input edge.

    // Y must equal (~(A|B)) & C_N & D_N.
    check_y_functional_equivalence: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N or posedge D_N or negedge D_N)
            (Y === ((~(A | B)) & C_N & D_N))
    );

    // If A and B are 0 and C_N and D_N are 1, Y must be 1.
    check_y_one_only_when_ab00_cn1_dn1: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N or posedge D_N or negedge D_N)
            ((!A && !B && (C_N == 1'b1) && (D_N == 1'b1)) -> (Y == 1'b1))
    );

    // A=1 forces Y=0.
    check_a_high_forces_y_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N or posedge D_N or negedge D_N)
            ((A == 1'b1) -> (Y == 1'b0))
    );

    // B=1 forces Y=0.
    check_b_high_forces_y_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N or posedge D_N or negedge D_N)
            ((B == 1'b1) -> (Y == 1'b0))
    );

    // C_N=0 forces Y=0.
    check_c_n_low_forces_y_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N or posedge D_N or negedge D_N)
            ((C_N == 1'b0) -> (Y == 1'b0))
    );

    // D_N=0 forces Y=0.
    check_d_n_low_forces_y_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N or posedge D_N or negedge D_N)
            ((D_N == 1'b0) -> (Y == 1'b0))
    );

    // Y=1 implies A=0.
    check_y_high_implies_a_zero: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N or posedge D_N or negedge D_N)
            ((Y == 1'b1) -> (A == 1'b0))
    );

    // Y=1 implies B=0.
    check_y_high_implies_b_zero: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N or posedge D_N or negedge D_N)
            ((Y == 1'b1) -> (B == 1'b0))
    );

    // With A=0 and B=0, Y equals C_N & D_N.
    check_ab00_y_equals_cn_and_dn: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N or posedge D_N or negedge D_N)
            ((!A && !B) -> (Y === (C_N & D_N)))
    );

    // With C_N=1 and D_N=1, Y equals ~(A|B).
    check_cn1_dn1_y_equals_nor_ab: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C_N or negedge C_N or posedge D_N or negedge D_N)
            (((C_N == 1'b1) && (D_N == 1'b1)) -> (Y === ~(A | B)))
    );
endmodule