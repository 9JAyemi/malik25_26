module sky130_fd_sc_ls__dlrtn_1_assertions (
    input logic Q,
    input logic RESET_B,
    input logic D,
    input logic GATE_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // No RTL clock is present; assertions sample on $global_clock.
    // RESET_B is active-high in this RTL.

    // RESET_B high has highest priority and drives Q low.
    check_reset_forces_q_low: assert property (
        @($global_clock) RESET_B |-> (Q == 1'b0)
    );

    // With reset inactive, GATE_N high makes Q follow D.
    check_gate_high_passes_d: assert property (
        @($global_clock) disable iff (RESET_B) GATE_N |-> (Q == D)
    );

    // With reset inactive, GATE_N low forces Q high.
    check_gate_low_forces_q_high: assert property (
        @($global_clock) disable iff (RESET_B) !GATE_N |-> (Q == 1'b1)
    );

    // With reset inactive, Q low can only come from passing D=0.
    check_q_low_requires_gate_high_and_d_low: assert property (
        @($global_clock) disable iff (RESET_B) (Q == 1'b0) |-> (GATE_N && !D)
    );

    // Q always matches the implemented combinational truth table.
    check_q_matches_truth_table: assert property (
        @($global_clock) Q == (RESET_B ? 1'b0 : (GATE_N ? D : 1'b1))
    );

endmodule