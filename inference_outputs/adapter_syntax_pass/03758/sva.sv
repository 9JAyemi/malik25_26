module autoasciienum_onehot_sva (
    input logic clk,
    input logic rst_n,
    input logic ack,
    input logic [4:0] cur_state,
    input logic [31:0] cur_state_ascii
);

    // Reset forces the FSM into IDLE.
    check_reset_state: assert property (
        @(posedge clk) !rst_n |-> (cur_state == 5'h1)
    );

    // Reset forces the ASCII decode to "idle".
    check_reset_ascii: assert property (
        @(posedge clk) !rst_n |-> (cur_state_ascii == "idle")
    );

    // IDLE transitions to S1 on the next clock.
    check_idle_to_s1: assert property (
        @(posedge clk) disable iff (!rst_n)
        (cur_state == 5'h0) |=> (cur_state == 5'h2)
    );

    // S1 transitions to S2 on the next clock.
    check_s1_to_s2: assert property (
        @(posedge clk) disable iff (!rst_n)
        (cur_state == 5'h2) |=> (cur_state == 5'h4)
    );

    // S2 transitions to S3 on the next clock.
    check_s2_to_s3: assert property (
        @(posedge clk) disable iff (!rst_n)
        (cur_state == 5'h4) |=> (cur_state == 5'h8)
    );

    // S3 transitions to DONE on the next clock.
    check_s3_to_done: assert property (
        @(posedge clk) disable iff (!rst_n)
        (cur_state == 5'h8) |=> (cur_state == 5'h10)
    );

    // DONE stays in DONE on the next clock.
    check_done_holds: assert property (
        @(posedge clk) disable iff (!rst_n)
        (cur_state == 5'h10) |=> (cur_state == 5'h10)
    );

    // ack is high exactly when the FSM is in DONE.
    check_ack_matches_done: assert property (
        @(posedge clk) disable iff (!rst_n)
        (ack == (cur_state == 5'h10))
    );

    // IDLE ASCII decode is "idle".
    check_idle_ascii: assert property (
        @(posedge clk) disable iff (!rst_n)
        (cur_state == 5'h0) |-> (cur_state_ascii == "idle")
    );

    // S1 ASCII decode is "s1  ".
    check_s1_ascii: assert property (
        @(posedge clk) disable iff (!rst_n)
        (cur_state == 5'h2) |-> (cur_state_ascii == "s1  ")
    );

    // S2 ASCII decode is "s2  ".
    check_s2_ascii: assert property (
        @(posedge clk) disable iff (!rst_n)
        (cur_state == 5'h4) |-> (cur_state_ascii == "s2  ")
    );

    // S3 ASCII decode is "s3  ".
    check_s3_ascii: assert property (
        @(posedge clk) disable iff (!rst_n)
        (cur_state == 5'h8) |-> (cur_state_ascii == "s3  ")
    );

    // DONE ASCII decode is "done".
    check_done_ascii: assert property (
        @(posedge clk) disable iff (!rst_n)
        (cur_state == 5'h10) |-> (cur_state_ascii == "done")
    );

    // Invalid state encodings decode to "%Err".
    check_default_ascii: assert property (
        @(posedge clk) disable iff (!rst_n)
        ((cur_state != 5'h0) && (cur_state != 5'h2) && (cur_state != 5'h4) &&
         (cur_state != 5'h8) && (cur_state != 5'h10)) |-> (cur_state_ascii == "%Err")
    );

endmodule