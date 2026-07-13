module my_circuit_sva (
    input logic Q,
    input logic CLK,
    input logic D,
    input logic SCD,
    input logic SCE,
    input logic SET_B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // Clock: CLK (posedge). No explicit reset in RTL. Sequential flop with priority: SET_B > SCD > SCE > hold.

    // Q follows the RTL next-state function based on last cycle controls.
    check_next_state_function: assert property (
        @(posedge CLK) disable iff ($initstate)
            Q == ( $past(SET_B) ? 1'b1 :
                   ($past(SCD) ? $past(D) :
                   ($past(SCE) ? 1'b0 : $past(Q))))
    );

    // If SET_B was 1 last cycle, Q must be 1 now.
    check_set_updates_one: assert property (
        @(posedge CLK) disable iff ($initstate)
            $past(SET_B) |-> (Q == 1'b1)
    );

    // If SCD was 1 last cycle with no SET_B, Q takes last D.
    check_capture_updates_q: assert property (
        @(posedge CLK) disable iff ($initstate)
            ($past(!SET_B) && $past(SCD)) |-> (Q == $past(D))
    );

    // If SCE was 1 last cycle with no SET_B or SCD, Q goes to 0.
    check_clear_updates_zero: assert property (
        @(posedge CLK) disable iff ($initstate)
            $past(!SET_B && !SCD && SCE) |-> (Q == 1'b0)
    );

    // If none were asserted last cycle, Q holds its value.
    check_hold_when_idle: assert property (
        @(posedge CLK) disable iff ($initstate)
            $past(!SET_B && !SCD && !SCE) |-> (Q == $past(Q))
    );

    // Q can change only if at least one control was 1 last cycle.
    check_change_requires_control: assert property (
        @(posedge CLK) disable iff ($initstate)
            (Q != $past(Q)) |-> $past(SET_B || SCD || SCE)
    );

    // SET_B has priority over SCD when both were 1 last cycle.
    check_set_over_scd: assert property (
        @(posedge CLK) disable iff ($initstate)
            $past(SET_B && SCD) |-> (Q == 1'b1)
    );

    // SET_B has priority over SCE when both were 1 last cycle.
    check_set_over_sce: assert property (
        @(posedge CLK) disable iff ($initstate)
            $past(SET_B && SCE) |-> (Q == 1'b1)
    );

    // SCD has priority over SCE when both were 1 last cycle and SET_B was 0.
    check_scd_over_sce: assert property (
        @(posedge CLK) disable iff ($initstate)
            $past(!SET_B && SCD && SCE) |-> (Q == $past(D))
    );

    // A 0->1 transition of Q implies SET_B or SCD with D==1 last cycle.
    check_rose_q_cause: assert property (
        @(posedge CLK) disable iff ($initstate)
            $rose(Q) |-> ($past(SET_B) || $past(!SET_B && SCD && D))
    );

    // A 1->0 transition of Q implies SCE or SCD with D==0 last cycle and no SET_B.
    check_fell_q_cause: assert property (
        @(posedge CLK) disable iff ($initstate)
            $fell(Q) |-> $past(!SET_B && (SCE || (SCD && !D)))
    );

endmodule