module autoasciienum_onehot_sva (
    input logic clk,
    input logic rst_n,
    input logic ack
);

// ack is HIGH exactly when the machine is in DONE state.
    check_ack_matches_done_state: assert property (
        @(posedge clk) disable iff (!rst_n) ack == (cur_state == DONE)
    );

// ack is LOW exactly when the machine is not in DONE state.
    check_ack_low_when_not_done: assert property (
        @(posedge clk) disable iff (!rst_n) !ack == (cur_state != DONE)
    );

// ack is HIGH exactly when the machine is not in IDLE state.
    check_ack_high_when_not_idle: assert property (
        @(posedge clk) disable iff (!rst_n) ack == (cur_state != IDLE)
    );

// ack is LOW exactly when the machine is in IDLE state.
    check_ack_low_when_idle: assert property (
        @(posedge clk) disable iff (!rst_n) !ack == (cur_state == IDLE)
    );

// ack is HIGH exactly when the machine is not in S1 state.
    check_ack_high_when_not_s1: assert property (
        @(posedge clk) disable iff (!rst_n) ack == (cur_state != S1)
    );

// ack is LOW exactly when the machine is in S1 state.
    check_ack_low_when_s1: assert property (
        @(posedge clk) disable iff (!rst_n) !ack == (cur_state == S1)
    );

// ack is HIGH exactly when the machine is not in S2 state.
    check_ack_high_when_not_s2: assert property (
        @(posedge clk) disable iff (!rst_n) ack == (cur_state != S2)
    );

// ack is LOW exactly when the machine is in S2 state.
    check_ack_low_when_s2: assert property (
        @(posedge clk) disable iff (!rst_n) !ack == (cur_state == S2)
    );

// ack is HIGH exactly when the machine is not in S3 state.
    check_ack_high_when_not_s3: assert property (
        @(posedge clk) disable iff (!rst_n) ack == (cur_state != S3)
    );

// ack is LOW exactly when the machine is in S3 state.
    check_ack_low_when_s3: assert property (
        @(posedge clk) disable iff (!rst_n) !ack == (cur_state == S3)
    );

endmodule
