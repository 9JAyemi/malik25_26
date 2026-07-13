module my_module_sva (
    input logic Q,
    input logic CLK,
    input logic D,
    input logic SCD,
    input logic SCE,
    input logic RESET_B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    ///// Environment assumptions (rails) /////
    // Constrain VPWR to be 0/1 (no X/Z) for formal convergence.
    env_vpwr_binary: assume property (
        @(posedge CLK) (VPWR === 1'b0) || (VPWR === 1'b1)
    );

    ///// Reset behavior /////
    // When RESET_B is LOW, Q must be 0 on the next clock.
    reset_low_forces_q0_next: assert property (
        @(posedge CLK) (RESET_B == 1'b0) |=> (Q == 1'b0)
    );
    // While RESET_B stays LOW across consecutive cycles, Q stays 0 and stable.
    reset_hold_q0_stable: assert property (
        @(posedge CLK) (RESET_B == 1'b0) && $past(RESET_B == 1'b0) |-> (Q == 1'b0) && $stable(Q)
    );
    // On a sampled falling edge of RESET_B, Q is 0 on the next clock.
    q_clears_on_reset_fall: assert property (
        @(posedge CLK) $fell(RESET_B) |=> (Q == 1'b0)
    );

    ///// Functional update rules (clocked, power good, reset deasserted) /////
    // After a cycle with power ON and reset deasserted, Q updates from either D or SCD.
    update_from_inputs_when_powered: assert property (
        @(posedge CLK) disable iff (RESET_B == 1'b0)
            $past((VPWR == 1'b1) && (RESET_B == 1'b1)) |-> ((Q == $past(D)) || (Q == $past(SCD)))
    );
    // When SCE was 0 last cycle under power ON and reset deasserted, Q follows D.
    follow_d_when_sce0: assert property (
        @(posedge CLK) disable iff (RESET_B == 1'b0)
            $past((VPWR == 1'b1) && (RESET_B == 1'b1) && (SCE == 1'b0)) |-> (Q == $past(D))
    );
    // When SCE was 1 last cycle under power ON and reset deasserted, Q follows SCD.
    follow_scd_when_sce1: assert property (
        @(posedge CLK) disable iff (RESET_B == 1'b0)
            $past((VPWR == 1'b1) && (RESET_B == 1'b1) && (SCE == 1'b1)) |-> (Q == $past(SCD))
    );
    // If D and SCD were equal last cycle in functional mode, Q equals that common value.
    follow_common_when_inputs_equal: assert property (
        @(posedge CLK) disable iff (RESET_B == 1'b0)
            $past((VPWR == 1'b1) && (RESET_B == 1'b1) && (D == SCD)) |-> (Q == $past(D))
    );
    // If inputs and select are stable over two functional cycles, Q is stable.
    stable_when_inputs_and_sel_stable: assert property (
        @(posedge CLK) disable iff (RESET_B == 1'b0)
            $past((VPWR == 1'b1) && (RESET_B == 1'b1)) &&
            (VPWR == 1'b1) && (RESET_B == 1'b1) &&
            $stable(D) && $stable(SCD) && $stable(SCE) |-> $stable(Q)
    );
endmodule