module my_module_sva (
    input logic CLK,
    input logic D,
    input logic SCD,
    input logic SCE,
    input logic SET_B,
    input logic EN,
    input logic Q
);
    // Exact next-state mapping for Q from previous-cycle controls and D.
    check_next_state_map: assert property (
        @(posedge CLK) $past(1'b1) |-> 
            Q == (
                ($past(EN)  == 1'b0) ? 1'b0 :
                ($past(SCD) == 1'b1) ? 1'b0 :
                ($past(SET_B)== 1'b1) ? 1'b1 :
                ($past(SCE) == 1'b1) ? $past(D) :
                $past(Q)
            )
    );

    // EN low synchronously clears Q to 0.
    check_clear_on_en_low: assert property (
        @(posedge CLK) $past(1'b1) && ($past(EN) == 1'b0) |-> (Q == 1'b0)
    );

    // With EN high, SCD high synchronously clears Q to 0.
    check_clear_on_scd: assert property (
        @(posedge CLK) $past(1'b1) && ($past(EN) == 1'b1) && ($past(SCD) == 1'b1) |-> (Q == 1'b0)
    );

    // With EN high and SCD low, SET_B high synchronously sets Q to 1.
    check_set_on_set_b: assert property (
        @(posedge CLK) $past(1'b1) && ($past(EN) == 1'b1) && ($past(SCD) == 1'b0) && ($past(SET_B) == 1'b1) |-> (Q == 1'b1)
    );

    // With higher-priority controls inactive, SCE high loads D into Q.
    check_load_on_sce: assert property (
        @(posedge CLK) $past(1'b1) && ($past(EN) == 1'b1) && ($past(SCD) == 1'b0) && ($past(SET_B) == 1'b0) && ($past(SCE) == 1'b1) |-> (Q == $past(D))
    );

    // When no control is active, Q holds its previous value.
    check_hold_when_no_ctrl: assert property (
        @(posedge CLK) $past(1'b1) && ($past(EN) == 1'b1) && ($past(SCD) == 1'b0) && ($past(SET_B) == 1'b0) && ($past(SCE) == 1'b0) |-> (Q == $past(Q))
    );

    // Q changes only if at least one control was active in the previous cycle.
    check_q_changes_only_with_ctrl: assert property (
        @(posedge CLK) $past(1'b1) && (Q != $past(Q)) |-> (($past(EN) == 1'b0) || ($past(SCD) == 1'b1) || ($past(SET_B) == 1'b1) || ($past(SCE) == 1'b1))
    );

    // A rising edge on Q comes only from SET_B or load of D==1 (with higher-priority clears inactive).
    check_q_rise_causes: assert property (
        @(posedge CLK) $past(1'b1) && $rose(Q) |-> 
            ( ($past(EN) == 1'b1) && ($past(SCD) == 1'b0) &&
              ( ($past(SET_B) == 1'b1) ||
                (($past(SET_B) == 1'b0) && ($past(SCE) == 1'b1) && ($past(D) == 1'b1)) ) )
    );

    // A falling edge on Q comes only from clears or load of D==0 (respecting priority).
    check_q_fall_causes: assert property (
        @(posedge CLK) $past(1'b1) && $fell(Q) |-> 
            ( ($past(EN) == 1'b0) ||
              (($past(EN) == 1'b1) && ($past(SCD) == 1'b1)) ||
              (($past(EN) == 1'b1) && ($past(SCD) == 1'b0) && ($past(SET_B) == 1'b0) && ($past(SCE) == 1'b1) && ($past(D) == 1'b0)) )
    );

    // SET_B has priority over SCE when both are high (with clears inactive).
    check_set_b_overrides_sce: assert property (
        @(posedge CLK) $past(1'b1) && ($past(EN) == 1'b1) && ($past(SCD) == 1'b0) && ($past(SET_B) == 1'b1) && ($past(SCE) == 1'b1) |-> (Q == 1'b1)
    );
endmodule