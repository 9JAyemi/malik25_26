module digital_circuit_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic Y,
    input logic [2:0] state
);
    localparam [2:0] IDLE                 = 3'b000;
    localparam [2:0] TRANSITION_ONE       = 3'b001;
    localparam [2:0] TRANSITION_TWO       = 3'b010;
    localparam [2:0] TRANSITION_THREE     = 3'b011;
    localparam [2:0] TRANSITION_COMPLETE  = 3'b100;

    ///// Output definition /////
    // Y high implies state is TRANSITION_COMPLETE.
    y_high_implies_state_tc: assert property (
        @(posedge VPWR) Y |-> (state === TRANSITION_COMPLETE)
    );
    // When state is TRANSITION_COMPLETE, Y must be high.
    state_tc_implies_y_high: assert property (
        @(posedge VPWR) (state === TRANSITION_COMPLETE) |-> (Y == 1'b1)
    );
    // Y can never be high for two consecutive VPWR cycles.
    y_is_single_cycle_pulse: assert property (
        @(posedge VPWR) Y |=> (Y == 1'b0)
    );

    ///// Next-state legality /////
    // From IDLE, next state is only IDLE or TRANSITION_ONE.
    idle_next_legal: assert property (
        @(posedge VPWR) (state === IDLE) |=> (state inside {IDLE, TRANSITION_ONE})
    );
    // From TRANSITION_ONE, next state is only TRANSITION_ONE or TRANSITION_TWO.
    t1_next_legal: assert property (
        @(posedge VPWR) (state === TRANSITION_ONE) |=> (state inside {TRANSITION_ONE, TRANSITION_TWO})
    );
    // From TRANSITION_TWO, next state is only TRANSITION_TWO or TRANSITION_THREE.
    t2_next_legal: assert property (
        @(posedge VPWR) (state === TRANSITION_TWO) |=> (state inside {TRANSITION_TWO, TRANSITION_THREE})
    );
    // From TRANSITION_THREE, next state is only TRANSITION_THREE or TRANSITION_COMPLETE.
    t3_next_legal: assert property (
        @(posedge VPWR) (state === TRANSITION_THREE) |=> (state inside {TRANSITION_THREE, TRANSITION_COMPLETE})
    );
    // From TRANSITION_COMPLETE, next state must be IDLE.
    tcomplete_to_idle: assert property (
        @(posedge VPWR) (state === TRANSITION_COMPLETE) |=> (state === IDLE)
    );

    ///// Progress on explicit conditions /////
    // From IDLE with all A/B low, go to TRANSITION_ONE.
    idle_progress_on_zeros: assert property (
        @(posedge VPWR) (state === IDLE) && (A1==1'b0 && A2==1'b0 && A3==1'b0 && B1==1'b0 && B2==1'b0)
        |=> (state === TRANSITION_ONE)
    );
    // From TRANSITION_ONE with all A/B high, go to TRANSITION_TWO.
    t1_progress_on_ones: assert property (
        @(posedge VPWR) (state === TRANSITION_ONE) && (A1==1'b1 && A2==1'b1 && A3==1'b1 && B1==1'b1 && B2==1'b1)
        |=> (state === TRANSITION_TWO)
    );
    // From TRANSITION_TWO with all A/B low, go to TRANSITION_THREE.
    t2_progress_on_zeros: assert property (
        @(posedge VPWR) (state === TRANSITION_TWO) && (A1==1'b0 && A2==1'b0 && A3==1'b0 && B1==1'b0 && B2==1'b0)
        |=> (state === TRANSITION_THREE)
    );
    // From TRANSITION_THREE with rails high and all A/B high, go to TRANSITION_COMPLETE.
    t3_progress_on_power_and_ones: assert property (
        @(posedge VPWR) (state === TRANSITION_THREE) &&
                         (VPWR==1'b1 && VPB==1'b1 && VNB==1'b1 && VGND==1'b1) &&
                         (A1==1'b1 && A2==1'b1 && A3==1'b1 && B1==1'b1 && B2==1'b1)
        |=> (state === TRANSITION_COMPLETE)
    );

    ///// Behavior for unrecognized states /////
    // In any non-enumerated state, hold value (no assignment in case/default).
    illegal_state_holds: assert property (
        @(posedge VPWR)
            ((state !== IDLE) && (state !== TRANSITION_ONE) && (state !== TRANSITION_TWO) &&
             (state !== TRANSITION_THREE) && (state !== TRANSITION_COMPLETE))
        |=> (state == $past(state))
    );

endmodule