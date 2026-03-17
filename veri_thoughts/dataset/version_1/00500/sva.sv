module fsm_3bit_pattern_detection_sva (
    input logic clk,
    input logic reset,
    input logic [5:0] data,
    input logic match,
    input logic [1:0] state,
    input logic [1:0] next_state
);

    localparam logic [1:0] S0 = 2'b00;
    localparam logic [1:0] S1 = 2'b01;
    localparam logic [1:0] S2 = 2'b10;
    localparam logic [1:0] S3 = 2'b11;

    // Reset forces the FSM to S0 and clears match.
    check_reset_state_and_match: assert property (
        @(posedge clk)
        reset |-> ((state == S0) && (match == 1'b0))
    );

    // In S0, only 001 on data[2:0] advances to S1.
    check_s0_next_state_decoding: assert property (
        @(posedge clk) disable iff (reset)
        (state == S0) |-> (next_state == ((data[2:0] == 3'b001) ? S1 : S0))
    );

    // In S1, only 010 on data[2:0] advances to S2.
    check_s1_next_state_decoding: assert property (
        @(posedge clk) disable iff (reset)
        (state == S1) |-> (next_state == ((data[2:0] == 3'b010) ? S2 : S0))
    );

    // In S2, only 100 on data[2:0] advances to S3.
    check_s2_next_state_decoding: assert property (
        @(posedge clk) disable iff (reset)
        (state == S2) |-> (next_state == ((data[2:0] == 3'b100) ? S3 : S0))
    );

    // In S3, the FSM always returns to S0.
    check_s3_next_state_decoding: assert property (
        @(posedge clk) disable iff (reset)
        (state == S3) |-> (next_state == S0)
    );

    // The state register loads next_state on each clock.
    check_state_register_update: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (state == $past(next_state))
    );

    // match reflects whether the previous cycle's state was S3.
    check_match_register_update: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (match == (($past(state) == S3) ? 1'b1 : 1'b0))
    );

    // A sampled S3 state produces S0 and match high on the next cycle.
    check_s3_returns_to_s0_with_match: assert property (
        @(posedge clk) disable iff (reset)
        (state == S3) |=> ((state == S0) && (match == 1'b1))
    );

    // A mismatch in S1 or S2 returns the FSM to S0 on the next cycle.
    check_mismatch_returns_to_s0: assert property (
        @(posedge clk) disable iff (reset)
        (((state == S1) && (data[2:0] != 3'b010)) ||
         ((state == S2) && (data[2:0] != 3'b100)))
        |=> (state == S0)
    );

    // 001,010,100 from S0 reaches S3 and then pulses match.
    check_full_pattern_detection: assert property (
        @(posedge clk) disable iff (reset)
        (
            ((state == S0) && (data[2:0] == 3'b001))
            ##1 ((state == S1) && (data[2:0] == 3'b010))
            ##1 ((state == S2) && (data[2:0] == 3'b100))
        )
        |=> (
            ((state == S3) && (match == 1'b0))
            ##1 ((state == S0) && (match == 1'b1))
        )
    );

endmodule