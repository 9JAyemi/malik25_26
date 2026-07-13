module SB_WARMBOOT_sva (
    input logic BOOT,
    input logic S1,
    input logic S0,
    input logic clk,
    input logic VALID,
    input logic [1:0] state,
    input logic [1:0] next_state
);
    // State encodings (match RTL)
    localparam logic [1:0] STATE_0 = 2'b00;
    localparam logic [1:0] STATE_1 = 2'b01;
    localparam logic [1:0] STATE_2 = 2'b10;
    localparam logic [1:0] STATE_3 = 2'b11;

    ///// Reset behavior /////
    // When BOOT is HIGH, next_state must be STATE_0 (combinational map).
    comb_reset_next_state: assert property (
        @(posedge clk) BOOT |-> (next_state == STATE_0)
    );

    // When BOOT is HIGH at a clock edge, state becomes STATE_0 on the next cycle (synchronous reset).
    sync_reset_state: assert property (
        @(posedge clk) BOOT |=> (state == STATE_0)
    );

    ///// State register update /////
    // When not in reset in consecutive cycles, state updates to the previous cycle's next_state.
    state_updates_from_next: assert property (
        @(posedge clk) disable iff (BOOT) !$past(BOOT) |-> (state == $past(next_state))
    );

    ///// Transition rules (when not in reset) /////
    // From STATE_0 with !S1 && S0, go to STATE_1 on next cycle.
    trans_s0_to_s1: assert property (
        @(posedge clk) disable iff (BOOT) (state == STATE_0 && !S1 && S0) |=> (state == STATE_1)
    );

    // From STATE_0 otherwise, hold in STATE_0 on next cycle.
    hold_s0_otherwise: assert property (
        @(posedge clk) disable iff (BOOT) (state == STATE_0 && !(!S1 && S0)) |=> (state == STATE_0)
    );

    // From STATE_1 with S1 && !S0, go to STATE_2 on next cycle.
    trans_s1_to_s2: assert property (
        @(posedge clk) disable iff (BOOT) (state == STATE_1 && S1 && !S0) |=> (state == STATE_2)
    );

    // From STATE_1 otherwise, hold in STATE_1 on next cycle.
    hold_s1_otherwise: assert property (
        @(posedge clk) disable iff (BOOT) (state == STATE_1 && !(S1 && !S0)) |=> (state == STATE_1)
    );

    // From STATE_2 with S1 && S0, go to STATE_3 on next cycle.
    trans_s2_to_s3: assert property (
        @(posedge clk) disable iff (BOOT) (state == STATE_2 && S1 && S0) |=> (state == STATE_3)
    );

    // From STATE_2 otherwise, hold in STATE_2 on next cycle.
    hold_s2_otherwise: assert property (
        @(posedge clk) disable iff (BOOT) (state == STATE_2 && !(S1 && S0)) |=> (state == STATE_2)
    );

    // From STATE_3 with !S1 && !S0, go to STATE_0 on next cycle.
    trans_s3_to_s0: assert property (
        @(posedge clk) disable iff (BOOT) (state == STATE_3 && !S1 && !S0) |=> (state == STATE_0)
    );

    // From STATE_3 otherwise, hold in STATE_3 on next cycle.
    hold_s3_otherwise: assert property (
        @(posedge clk) disable iff (BOOT) (state == STATE_3 && !(!S1 && !S0)) |=> (state == STATE_3)
    );

    ///// Output behavior /////
    // VALID remains HIGH when not in reset.
    valid_always_high_run: assert property (
        @(posedge clk) disable iff (BOOT) (VALID == 1'b1)
    );

    // VALID never falls when not in reset.
    valid_no_fall_run: assert property (
        @(posedge clk) disable iff (BOOT) !$fell(VALID)
    );

    // After reset deasserts, VALID is HIGH.
    valid_after_reset_release: assert property (
        @(posedge clk) $fell(BOOT) |-> (VALID == 1'b1)
    );

endmodule