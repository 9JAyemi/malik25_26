module sky130_fd_sc_hd__nand4bb_sva (
    input  logic A_N,
    input  logic B_N,
    input  logic C,
    input  logic D,
    input  logic Y,
    input  logic VPB,
    input  logic VPWR,
    input  logic VGND,
    input  logic VNB
);
    // Y matches NAND(A_N,B_N,C,D) when A_N rises.
    check_nand_eq_on_A_N: assert property (
        @(posedge A_N) Y == ~(A_N & B_N & C & D)
    );

    // Y matches NAND(A_N,B_N,C,D) when B_N rises.
    check_nand_eq_on_B_N: assert property (
        @(posedge B_N) Y == ~(A_N & B_N & C & D)
    );

    // Y matches NAND(A_N,B_N,C,D) when C rises.
    check_nand_eq_on_C: assert property (
        @(posedge C) Y == ~(A_N & B_N & C & D)
    );

    // Y matches NAND(A_N,B_N,C,D) when D rises.
    check_nand_eq_on_D: assert property (
        @(posedge D) Y == ~(A_N & B_N & C & D)
    );

    // Any fall on A_N forces Y high in the same cycle.
    check_y_high_on_fall_A_N: assert property (
        @(negedge A_N) Y == 1'b1
    );

    // Any fall on B_N forces Y high in the same cycle.
    check_y_high_on_fall_B_N: assert property (
        @(negedge B_N) Y == 1'b1
    );

    // Any fall on C forces Y high in the same cycle.
    check_y_high_on_fall_C: assert property (
        @(negedge C) Y == 1'b1
    );

    // Any fall on D forces Y high in the same cycle.
    check_y_high_on_fall_D: assert property (
        @(negedge D) Y == 1'b1
    );

    // Y falling implies all inputs are HIGH.
    check_y_fall_requires_all_high: assert property (
        @(negedge Y) (A_N & B_N & C & D)
    );

    // Y rising implies not all inputs are HIGH.
    check_y_rise_implies_not_all_high: assert property (
        @(posedge Y) !(A_N & B_N & C & D)
    );
endmodule