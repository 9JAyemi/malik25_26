module up_counter_sva (
    input logic clk,
    input logic reset,    // Synchronous active-high reset
    input logic ena,      // Synchronous active-high enable
    input logic [15:0] q,
    // Optional internal connections for deeper checks (bind hierarchically if available)
    input logic [1:0] state,
    input logic [1:0] next_state,
    input logic [15:0] count_reg
);
    // Mirror DUT state encodings
    localparam logic [1:0] IDLE = 2'b00;
    localparam logic [1:0] COUNT = 2'b01;
    localparam logic [1:0] COUNT_BY_TWO = 2'b10;

    ///// Reset behavior /////
    // On reset, q is cleared to 0.
    reset_clears_q: assert property (
        @(posedge clk) reset |-> (q == 16'd0)
    );
    // On reset, state is IDLE.
    reset_sets_state_idle: assert property (
        @(posedge clk) reset |-> (state == IDLE)
    );

    ///// Output mapping /////
    // q directly reflects count_reg.
    q_matches_count_reg: assert property (
        @(posedge clk) (q == count_reg)
    );

    ///// Counter update rules /////
    // When disabled, q holds its previous value.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset) (!ena) |-> (q == $past(q))
    );
    // From IDLE with enable, q is forced to 0.
    zero_on_enable_from_idle: assert property (
        @(posedge clk) disable iff (reset) (ena && ($past(state) == IDLE)) |-> (q == 16'd0)
    );
    // In COUNT with enable, q increments by 1.
    inc_by_one_in_count: assert property (
        @(posedge clk) disable iff (reset) (ena && ($past(state) == COUNT)) |-> (q == $past(q) + 16'd1)
    );
    // In COUNT_BY_TWO with enable, q increments by 2.
    inc_by_two_in_count_by_two: assert property (
        @(posedge clk) disable iff (reset) (ena && ($past(state) == COUNT_BY_TWO)) |-> (q == $past(q) + 16'd2)
    );

    ///// Registered state transitions /////
    // With enable in IDLE, next registered state is COUNT.
    state_idle_to_count: assert property (
        @(posedge clk) disable iff (reset) (($past(state) == IDLE) && ena) |-> (state == COUNT)
    );
    // With enable in COUNT, next registered state is COUNT_BY_TWO.
    state_count_to_cbt: assert property (
        @(posedge clk) disable iff (reset) (($past(state) == COUNT) && ena) |-> (state == COUNT_BY_TWO)
    );
    // With enable in COUNT_BY_TWO, next registered state is COUNT.
    state_cbt_to_count: assert property (
        @(posedge clk) disable iff (reset) (($past(state) == COUNT_BY_TWO) && ena) |-> (state == COUNT)
    );
    // When disabled, next registered state is IDLE.
    state_to_idle_when_disabled: assert property (
        @(posedge clk) disable iff (reset) (($past(state) inside {IDLE, COUNT, COUNT_BY_TWO}) && !ena) |-> (state == IDLE)
    );

    ///// Combinational next_state logic (checked on clock edge) /////
    // IDLE & !ena -> next_state = IDLE.
    next_state_idle_when_disabled: assert property (
        @(posedge clk) disable iff (reset) (state == IDLE && !ena) |-> (next_state == IDLE)
    );
    // IDLE & ena -> next_state = COUNT.
    next_state_idle_enable_to_count: assert property (
        @(posedge clk) disable iff (reset) (state == IDLE && ena) |-> (next_state == COUNT)
    );
    // COUNT & !ena -> next_state = IDLE.
    next_state_count_disabled_to_idle: assert property (
        @(posedge clk) disable iff (reset) (state == COUNT && !ena) |-> (next_state == IDLE)
    );
    // COUNT & ena -> next_state = COUNT_BY_TWO.
    next_state_count_enable_to_cbt: assert property (
        @(posedge clk) disable iff (reset) (state == COUNT && ena) |-> (next_state == COUNT_BY_TWO)
    );
    // COUNT_BY_TWO & !ena -> next_state = IDLE.
    next_state_cbt_disabled_to_idle: assert property (
        @(posedge clk) disable iff (reset) (state == COUNT_BY_TWO && !ena) |-> (next_state == IDLE)
    );
    // COUNT_BY_TWO & ena -> next_state = COUNT.
    next_state_cbt_enable_to_count: assert property (
        @(posedge clk) disable iff (reset) (state == COUNT_BY_TWO && ena) |-> (next_state == COUNT)
    );
    // Registered state follows previous-cycle next_state when not in reset.
    state_follows_next_state: assert property (
        @(posedge clk) disable iff (reset) (state == $past(next_state))
    );

endmodule