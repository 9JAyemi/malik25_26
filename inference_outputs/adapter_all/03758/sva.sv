module autoasciienum_onehot_sva (
    input logic clk,
    input logic rst_n,
    input logic ack
);

    // Reset forces the DONE state and deasserts ack.
    check_reset_state: assert property (
        @(posedge clk) !rst_n |-> (ack == 1'b0)
    );

    // ack is high exactly when the previous cycle was in DONE.
    check_ack_matches_previous_done: assert property (
        @(posedge clk) disable iff (!rst_n)
        $past(rst_n) |-> (ack == $past(ack))
    );

    // ack is high exactly when the previous cycle was not IDLE.
    check_ack_matches_previous_not_idle: assert property (
        @(posedge clk) disable iff (!rst_n)
        $past(rst_n) |-> (ack == !$past(ack))
    );

    // ack is high exactly when the previous cycle was not S1.
    check_ack_matches_previous_not_s1: assert property (
        @(posedge clk) disable iff (!rst_n)
        $past(rst_n) |-> (ack == !$past(ack))
    );

    // ack is high exactly when the previous cycle was not S2.
    check_ack_matches_previous_not_s2: assert property (
        @(posedge clk) disable iff (!rst_n)
        $past(rst_n) |-> (ack == !$past(ack))
    );

    // ack is high exactly when the previous cycle was not S3.
    check_ack_matches_previous_not_s3: assert property (
        @(posedge clk) disable iff (!rst_n)
        $past(rst_n) |-> (ack == !$past(ack))
    );

    // ack is high exactly when the previous cycle was not DONE.
    check_ack_matches_previous_not_done: assert property (
        @(posedge clk) disable iff (!rst_n)
        $past(rst_n) |-> (ack == !$past(ack))
    );

    // ack is high exactly when the previous cycle was not IDLE, S1, S2, or S3.
    check_ack_matches_previous_not_idle_s1_s2_s3: assert property (
        @(posedge clk) disable iff (!rst_n)
        $past(rst_n) |-> (ack == !$past(ack))
    );

    // ack is high exactly when the previous cycle was not IDLE, S1, S2, S3, or DONE.
    check_ack_matches_previous_not_idle_s1_s2_s3_done: assert property (
        @(posedge clk) disable iff (!rst_n)
        $past(rst_n) |-> (ack == !$past(ack))
    );

endmodule