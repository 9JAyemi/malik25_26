module autoasciienum_onehot_sva (
    input logic        clk,
    input logic        rst_n,
    input logic        ack,
    input logic [4:0]  cur_state,
    input logic [4:0]  nxt_state,
    input logic [31:0] cur_state_ascii
);

    localparam int IDLE = 0;
    localparam int S1   = 1;
    localparam int S2   = 2;
    localparam int S3   = 3;
    localparam int DONE = 4;

    localparam logic [4:0] ST_IDLE = 5'b00001;
    localparam logic [4:0] ST_S1   = 5'b00010;
    localparam logic [4:0] ST_S2   = 5'b00100;
    localparam logic [4:0] ST_S3   = 5'b01000;
    localparam logic [4:0] ST_DONE = 5'b10000;

    // Reset forces the state register to IDLE.
    check_reset_sets_idle: assert property (
        @(posedge clk) !rst_n |-> (cur_state == ST_IDLE)
    );

    // Reset keeps ack low.
    check_reset_clears_ack: assert property (
        @(posedge clk) !rst_n |-> (ack == 1'b0)
    );

    // ack is always the DONE state bit.
    check_ack_matches_done_bit: assert property (
        @(posedge clk) disable iff (!rst_n) (ack == cur_state[DONE])
    );

    // IDLE decodes to S1 in the next-state logic.
    check_idle_nxt_state_decode: assert property (
        @(posedge clk) disable iff (!rst_n) (cur_state == ST_IDLE) |-> (nxt_state == ST_S1)
    );

    // S1 decodes to S2 in the next-state logic.
    check_s1_nxt_state_decode: assert property (
        @(posedge clk) disable iff (!rst_n) (cur_state == ST_S1) |-> (nxt_state == ST_S2)
    );

    // S2 decodes to S3 in the next-state logic.
    check_s2_nxt_state_decode: assert property (
        @(posedge clk) disable iff (!rst_n) (cur_state == ST_S2) |-> (nxt_state == ST_S3)
    );

    // S3 decodes to DONE in the next-state logic.
    check_s3_nxt_state_decode: assert property (
        @(posedge clk) disable iff (!rst_n) (cur_state == ST_S3) |-> (nxt_state == ST_DONE)
    );

    // DONE remains DONE in the next-state logic.
    check_done_nxt_state_decode: assert property (
        @(posedge clk) disable iff (!rst_n) (cur_state == ST_DONE) |-> (nxt_state == ST_DONE)
    );

    // IDLE advances to S1 on the next clock.
    check_idle_advances_to_s1: assert property (
        @(posedge clk) disable iff (!rst_n) (cur_state == ST_IDLE) |=> (cur_state == ST_S1)
    );

    // S1 advances to S2 on the next clock.
    check_s1_advances_to_s2: assert property (
        @(posedge clk) disable iff (!rst_n) (cur_state == ST_S1) |=> (cur_state == ST_S2)
    );

    // S2 advances to S3 on the next clock.
    check_s2_advances_to_s3: assert property (
        @(posedge clk) disable iff (!rst_n) (cur_state == ST_S2) |=> (cur_state == ST_S3)
    );

    // S3 advances to DONE on the next clock.
    check_s3_advances_to_done: assert property (
        @(posedge clk) disable iff (!rst_n) (cur_state == ST_S3) |=> (cur_state == ST_DONE)
    );

    // DONE holds on the next clock.
    check_done_holds_state: assert property (
        @(posedge clk) disable iff (!rst_n) (cur_state == ST_DONE) |=> (cur_state == ST_DONE)
    );

    // IDLE decodes to ASCII "idle".
    check_idle_ascii_decode: assert property (
        @(posedge clk) disable iff (!rst_n) (cur_state == ST_IDLE) |-> (cur_state_ascii == "idle")
    );

    // S1 decodes to ASCII "s1  ".
    check_s1_ascii_decode: assert property (
        @(posedge clk) disable iff (!rst_n) (cur_state == ST_S1) |-> (cur_state_ascii == "s1  ")
    );

    // S2 decodes to ASCII "s2  ".
    check_s2_ascii_decode: assert property (
        @(posedge clk) disable iff (!rst_n) (cur_state == ST_S2) |-> (cur_state_ascii == "s2  ")
    );

    // S3 decodes to ASCII "s3  ".
    check_s3_ascii_decode: assert property (
        @(posedge clk) disable iff (!rst_n) (cur_state == ST_S3) |-> (cur_state_ascii == "s3  ")
    );

    // DONE decodes to ASCII "done".
    check_done_ascii_decode: assert property (
        @(posedge clk) disable iff (!rst_n) (cur_state == ST_DONE) |-> (cur_state_ascii == "done")
    );

    // Invalid encodings decode to ASCII "%Err".
    check_invalid_ascii_decode: assert property (
        @(posedge clk) disable iff (!rst_n)
        (cur_state != ST_IDLE && cur_state != ST_S1 && cur_state != ST_S2 &&
         cur_state != ST_S3   && cur_state != ST_DONE) |-> (cur_state_ascii == "%Err")
    );

endmodule