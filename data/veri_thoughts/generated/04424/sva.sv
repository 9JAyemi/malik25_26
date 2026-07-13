module fsm_4bit_sequence_detection_sva (
    input logic clk,
    input logic [3:0] in,
    input logic match,
    input logic [1:0] state
);

    localparam [1:0] IDLE   = 2'b00;
    localparam [1:0] STATE1 = 2'b01;
    localparam [1:0] STATE2 = 2'b10;
    localparam [1:0] MATCH  = 2'b11;

    // MATCH state drives match high.
    check_match_high_in_match_state: assert property (
        @(posedge clk) (state == MATCH) |-> (match == 1'b1)
    );

    // Non-MATCH states drive match low.
    check_match_low_outside_match_state: assert property (
        @(posedge clk) (state != MATCH) |-> (match == 1'b0)
    );

    // IDLE advances to STATE1 on input 0001.
    check_idle_to_state1_on_0001: assert property (
        @(posedge clk) (state == IDLE && in == 4'b0001) |=> (state == STATE1)
    );

    // IDLE stays in IDLE on any other input.
    check_idle_stays_idle_on_other_inputs: assert property (
        @(posedge clk) (state == IDLE && in != 4'b0001) |=> (state == IDLE)
    );

    // STATE1 advances to STATE2 on input 0000.
    check_state1_to_state2_on_0000: assert property (
        @(posedge clk) (state == STATE1 && in == 4'b0000) |=> (state == STATE2)
    );

    // STATE1 returns to IDLE on any other input.
    check_state1_returns_idle_on_other_inputs: assert property (
        @(posedge clk) (state == STATE1 && in != 4'b0000) |=> (state == IDLE)
    );

    // STATE2 advances to MATCH on input 0001.
    check_state2_to_match_on_0001: assert property (
        @(posedge clk) (state == STATE2 && in == 4'b0001) |=> (state == MATCH)
    );

    // STATE2 returns to IDLE on any other input.
    check_state2_returns_idle_on_other_inputs: assert property (
        @(posedge clk) (state == STATE2 && in != 4'b0001) |=> (state == IDLE)
    );

    // MATCH always returns to IDLE on the next clock.
    check_match_returns_to_idle: assert property (
        @(posedge clk) (state == MATCH) |=> (state == IDLE)
    );

    // match is a one-cycle pulse.
    check_match_is_single_cycle_pulse: assert property (
        @(posedge clk) (match == 1'b1) |=> (match == 1'b0)
    );

endmodule