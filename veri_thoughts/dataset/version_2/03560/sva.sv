module sky130_fd_sc_ls__nor4bb_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N
);

    // Y must match the implemented NOR followed by AND function.
    check_y_function: assert property (
        @($global_clock) Y === ((~(A | B)) & C_N & D_N)
    );

    // A high forces the NOR output low, so Y must be low.
    check_a_high_forces_y_low: assert property (
        @($global_clock) (A === 1'b1) |-> (Y === 1'b0)
    );

    // B high forces the NOR output low, so Y must be low.
    check_b_high_forces_y_low: assert property (
        @($global_clock) (B === 1'b1) |-> (Y === 1'b0)
    );

    // C_N low blocks the final AND, so Y must be low.
    check_cn_low_forces_y_low: assert property (
        @($global_clock) (C_N === 1'b0) |-> (Y === 1'b0)
    );

    // D_N low blocks the final AND, so Y must be low.
    check_dn_low_forces_y_low: assert property (
        @($global_clock) (D_N === 1'b0) |-> (Y === 1'b0)
    );

    // The only high-output input combination must drive Y high.
    check_all_conditions_true_drive_y_high: assert property (
        @($global_clock)
        ((A === 1'b0) && (B === 1'b0) && (C_N === 1'b1) && (D_N === 1'b1)) |-> (Y === 1'b1)
    );

    // If Y is high, all required input conditions must be present.
    check_y_high_implies_required_inputs: assert property (
        @($global_clock)
        (Y === 1'b1) |-> ((A === 1'b0) && (B === 1'b0) && (C_N === 1'b1) && (D_N === 1'b1))
    );

    // With A and B low, Y reduces to C_N AND D_N.
    check_ab_low_reduces_to_cn_and_dn: assert property (
        @($global_clock)
        ((A === 1'b0) && (B === 1'b0)) |-> (Y === (C_N & D_N))
    );

    // With C_N and D_N high, Y reduces to NOR(A,B).
    check_cn_dn_high_reduces_to_nor_ab: assert property (
        @($global_clock)
        ((C_N === 1'b1) && (D_N === 1'b1)) |-> (Y === ~(A | B))
    );

endmodule