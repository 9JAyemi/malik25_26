module binary_counter_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [3:0] count,
    input logic [1:0] state,
    input logic [1:0] next_state,
    input logic [3:0] counter
);
    // State encodings from RTL
    localparam logic [1:0] IDLE  = 2'b00;
    localparam logic [1:0] COUNT = 2'b01;

    // Output mirrors internal counter.
    check_count_mirrors_counter: assert property (
        @(posedge clk) count == counter
    );

    // While reset is asserted low, state must be IDLE.
    check_state_idle_during_reset: assert property (
        @(posedge clk) (reset == 1'b0) |-> (state == IDLE)
    );

    // When not in reset, state updates from previous next_state.
    check_state_follows_next_state: assert property (
        @(posedge clk) disable iff (reset == 1'b0) state == $past(next_state)
    );

    // next_state only takes defined encodings.
    check_next_state_enum: assert property (
        @(posedge clk) disable iff (reset == 1'b0) next_state inside {IDLE, COUNT}
    );

    // state only takes defined encodings when not in reset.
    check_state_enum: assert property (
        @(posedge clk) disable iff (reset == 1'b0) state inside {IDLE, COUNT}
    );

    // In IDLE with enable=1, next_state is COUNT.
    check_idle_enable_to_count: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (state == IDLE && enable) |-> (next_state == COUNT)
    );

    // In IDLE with enable=0, next_state is IDLE.
    check_idle_no_enable_stays_idle: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (state == IDLE && !enable) |-> (next_state == IDLE)
    );

    // In COUNT with counter==15, next_state is IDLE.
    check_count_max_to_idle: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (state == COUNT && counter == 4'hF) |-> (next_state == IDLE)
    );

    // In COUNT with counter!=15, next_state is COUNT.
    check_count_not_max_stays_count: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (state == COUNT && counter != 4'hF) |-> (next_state == COUNT)
    );

    // One-cycle: IDLE with enable=0 leads to state IDLE.
    check_idle_enable0_next_state_idle: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (state == IDLE && !enable) |=> (state == IDLE)
    );

    // One-cycle: IDLE with enable=1 leads to state COUNT.
    check_idle_enable1_next_state_count: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (state == IDLE && enable) |=> (state == COUNT)
    );

    // One-cycle: COUNT with counter==15 leads to state IDLE.
    check_count_max_next_state_idle: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (state == COUNT && counter == 4'hF) |=> (state == IDLE)
    );

    // One-cycle: COUNT with counter!=15 leads to state COUNT.
    check_count_notmax_next_state_count: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (state == COUNT && counter != 4'hF) |=> (state == COUNT)
    );

    // If state is an unknown encoding, default drives next_state to IDLE.
    check_default_next_state_idle: assert property (
        @(posedge clk) disable iff (reset == 1'b0) (!(state inside {IDLE, COUNT})) |-> (next_state == IDLE)
    );
endmodule