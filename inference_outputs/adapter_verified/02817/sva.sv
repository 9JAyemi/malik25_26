module altera_tse_xcvr_resync_sva (
    input logic              clk,
    input logic [WIDTH-1:0]  d,
    input logic [WIDTH-1:0]  q
);

// q[0] follows d[0] with a latency of SYNC_CHAIN_LENGTH.
    check_q0_latency: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |-> ##(SYNC_CHAIN_LENGTH) (q[0] == $past(d[0], SYNC_CHAIN_LENGTH))
    );

// q[1] follows d[1] with a latency of SYNC_CHAIN_LENGTH.
    check_q1_latency: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |-> ##(SYNC_CHAIN_LENGTH) (q[1] == $past(d[1], SYNC_CHAIN_LENGTH))
    );

// q[2] follows d[2] with a latency of SYNC_CHAIN_LENGTH.
    check_q2_latency: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |-> ##(SYNC_CHAIN_LENGTH) (q[2] == $past(d[2], SYNC_CHAIN_LENGTH))
    );

// q[3] follows d[3] with a latency of SYNC_CHAIN_LENGTH.
    check_q3_latency: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |-> ##(SYNC_CHAIN_LENGTH) (q[3] == $past(d[3], SYNC_CHAIN_LENGTH))
    );

// q[4] follows d[4] with a latency of SYNC_CHAIN_LENGTH.
    check_q4_latency: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |-> ##(SYNC_CHAIN_LENGTH) (q[4] == $past(d[4], SYNC_CHAIN_LENGTH))
    );

// q[5] follows d[5] with a latency of SYNC_CHAIN_LENGTH.
    check_q5_latency: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |-> ##(SYNC_CHAIN_LENGTH) (q[5] == $past(d[5], SYNC_CHAIN_LENGTH))
    );

// q[6] follows d[6] with a latency of SYNC_CHAIN_LENGTH.
    check_q6_latency: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |-> ##(SYNC_CHAIN_LENGTH) (q[6] == $past(d[6], SYNC_CHAIN_LENGTH))
    );

// q[7] follows d[7] with a latency of SYNC_CHAIN_LENGTH.
    check_q7_latency: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |-> ##(SYNC_CHAIN_LENGTH) (q[7] == $past(d[7], SYNC_CHAIN_LENGTH))
    );

endmodule
