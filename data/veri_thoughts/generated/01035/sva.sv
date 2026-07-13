module sky130_fd_sc_lp__nor4bb_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N
);
    // Y equals (~(A|B)) & C_N & D_N when inputs are known.
    check_logic_equation: assert property (
        @(posedge clk) !$isunknown({A,B,C_N,D_N}) |-> (Y == ((~(A | B)) & C_N & D_N))
    );

    // Y can be HIGH only when A=0, B=0, C_N=1, D_N=1.
    check_y_high_implies_inputs: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((A == 1'b0) && (B == 1'b0) && (C_N == 1'b1) && (D_N == 1'b1))
    );

    // A=1 forces Y=0.
    check_a_high_forces_y_low: assert property (
        @(posedge clk) (A == 1'b1) |-> (Y == 1'b0)
    );

    // B=1 forces Y=0.
    check_b_high_forces_y_low: assert property (
        @(posedge clk) (B == 1'b1) |-> (Y == 1'b0)
    );

    // C_N=0 forces Y=0.
    check_cn_low_forces_y_low: assert property (
        @(posedge clk) (C_N == 1'b0) |-> (Y == 1'b0)
    );

    // D_N=0 forces Y=0.
    check_dn_low_forces_y_low: assert property (
        @(posedge clk) (D_N == 1'b0) |-> (Y == 1'b0)
    );

    // When A=0, B=0, C_N=1, and D_N=1, Y must be 1.
    check_all_conditions_drive_y_high: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b0) && (C_N == 1'b1) && (D_N == 1'b1)) |-> (Y == 1'b1)
    );

    // A rising edge drives Y low in the same cycle.
    check_rose_a_drives_y_low: assert property (
        @(posedge clk) $rose(A) |-> (Y == 1'b0)
    );

    // B rising edge drives Y low in the same cycle.
    check_rose_b_drives_y_low: assert property (
        @(posedge clk) $rose(B) |-> (Y == 1'b0)
    );

    // C_N falling edge drives Y low in the same cycle.
    check_fell_cn_drives_y_low: assert property (
        @(posedge clk) $fell(C_N) |-> (Y == 1'b0)
    );

    // D_N falling edge drives Y low in the same cycle.
    check_fell_dn_drives_y_low: assert property (
        @(posedge clk) $fell(D_N) |-> (Y == 1'b0)
    );
endmodule