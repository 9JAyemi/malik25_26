module sky130_fd_sc_hd__nor4b_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic Y
);

`define NOR4B_ANY_EDGE \
    posedge A or negedge A or \
    posedge B or negedge B or \
    posedge C or negedge C or \
    posedge D_N or negedge D_N or \
    posedge VPWR or negedge VPWR or \
    posedge VGND or negedge VGND or \
    posedge VPB or negedge VPB or \
    posedge VNB or negedge VNB or \
    posedge Y or negedge Y

// Y must match the RTL NOR equation.
check_y_matches_nor_function: assert property (
    @(`NOR4B_ANY_EDGE) disable iff (1'b0)
    Y == ~(A | B | C | D_N)
);

// All logic inputs low drives Y high.
check_all_inputs_low_drive_y_high: assert property (
    @(`NOR4B_ANY_EDGE) disable iff (1'b0)
    (!A && !B && !C && !D_N) |-> Y
);

// A high forces Y low.
check_a_high_forces_y_low: assert property (
    @(`NOR4B_ANY_EDGE) disable iff (1'b0)
    A |-> !Y
);

// B high forces Y low.
check_b_high_forces_y_low: assert property (
    @(`NOR4B_ANY_EDGE) disable iff (1'b0)
    B |-> !Y
);

// C high forces Y low.
check_c_high_forces_y_low: assert property (
    @(`NOR4B_ANY_EDGE) disable iff (1'b0)
    C |-> !Y
);

// D_N high forces Y low.
check_d_n_high_forces_y_low: assert property (
    @(`NOR4B_ANY_EDGE) disable iff (1'b0)
    D_N |-> !Y
);

// Stable logic inputs must keep Y stable.
check_stable_logic_inputs_hold_y: assert property (
    @(`NOR4B_ANY_EDGE) disable iff (1'b0)
    ($stable(A) && $stable(B) && $stable(C) && $stable(D_N)) |-> $stable(Y)
);

// Power-pin changes alone cannot affect Y in this RTL.
check_power_pin_activity_does_not_change_y: assert property (
    @(posedge VPWR or negedge VPWR or
      posedge VGND or negedge VGND or
      posedge VPB  or negedge VPB  or
      posedge VNB  or negedge VNB) disable iff (1'b0)
    ($stable(A) && $stable(B) && $stable(C) && $stable(D_N)) |-> $stable(Y)
);

endmodule