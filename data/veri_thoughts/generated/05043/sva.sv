module fsm_consecutive_ones_counter_sva (
    input logic clk,
    input logic reset,
    input logic data,
    input logic match,
    input logic [1:0] state
);

    localparam logic [1:0] S0 = 2'b00;
    localparam logic [1:0] S1 = 2'b01;
    localparam logic [1:0] S2 = 2'b10;
    localparam logic [1:0] S3 = 2'b11;

    // Reset forces the FSM to S0 and clears match.
    check_reset_state_and_match: assert property (
        @(posedge clk) !reset |-> (state == S0 && match == 1'b0)
    );

    // In S0 with data low, the FSM stays in S0.
    check_s0_data0_stays_s0: assert property (
        @(posedge clk) disable iff (!reset)
        (state == S0 && data == 1'b0) |=> (state == S0)
    );

    // In S0 with data high, the FSM advances to S1.
    check_s0_data1_to_s1: assert property (
        @(posedge clk) disable iff (!reset)
        (state == S0 && data == 1'b1) |=> (state == S1)
    );

    // In S1 with data low, the FSM returns to S0.
    check_s1_data0_to_s0: assert property (
        @(posedge clk) disable iff (!reset)
        (state == S1 && data == 1'b0) |=> (state == S0)
    );

    // In S1 with data high, the FSM advances to S2.
    check_s1_data1_to_s2: assert property (
        @(posedge clk) disable iff (!reset)
        (state == S1 && data == 1'b1) |=> (state == S2)
    );

    // In S2 with data low, the FSM returns to S0.
    check_s2_data0_to_s0: assert property (
        @(posedge clk) disable iff (!reset)
        (state == S2 && data == 1'b0) |=> (state == S0)
    );

    // In S2 with data high, the FSM advances to S3.
    check_s2_data1_to_s3: assert property (
        @(posedge clk) disable iff (!reset)
        (state == S2 && data == 1'b1) |=> (state == S3)
    );

    // In S3 with data low, the FSM stays in S3.
    check_s3_data0_stays_s3: assert property (
        @(posedge clk) disable iff (!reset)
        (state == S3 && data == 1'b0) |=> (state == S3)
    );

    // In S3 with data high, the FSM wraps back to S0.
    check_s3_data1_to_s0: assert property (
        @(posedge clk) disable iff (!reset)
        (state == S3 && data == 1'b1) |=> (state == S0)
    );

    // Match must be high whenever the FSM is in S3.
    check_match_high_in_s3: assert property (
        @(posedge clk) disable iff (!reset)
        (state == S3) |-> (match == 1'b1)
    );

    // Match must be low in all non-S3 states.
    check_match_low_outside_s3: assert property (
        @(posedge clk) disable iff (!reset)
        (state == S0 || state == S1 || state == S2) |-> (match == 1'b0)
    );

endmodule