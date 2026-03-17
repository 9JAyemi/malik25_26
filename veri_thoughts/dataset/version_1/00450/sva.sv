module db_controller_sva (
    input logic       clk,
    input logic       rst_n,
    input logic       start_i,
    input logic       done_o,
    input logic [8:0] cnt_r,
    input logic [2:0] state
);

    localparam [2:0] IDLE  = 3'b000;
    localparam [2:0] LOAD  = 3'b001;
    localparam [2:0] YHOR  = 3'b010;
    localparam [2:0] YVER  = 3'b011;
    localparam [2:0] OUT   = 3'b100;
    localparam [2:0] OUTLT = 3'b101;
    localparam [2:0] CVER  = 3'b110;
    localparam [2:0] CHOR  = 3'b111;

    localparam [8:0] LOAD_CYCLES  = 9'd384;
    localparam [8:0] YVER_CYCLES  = 9'd132;
    localparam [8:0] YHOR_CYCLES  = 9'd140;
    localparam [8:0] CVER_CYCLES  = 9'd68;
    localparam [8:0] CHOR_CYCLES  = 9'd76;
    localparam [8:0] OUTLT_CYCLES = 9'd67;
    localparam [8:0] OUT_CYCLES   = 9'd384;

    // Formal starts with reset asserted.
    init_starts_in_reset: assume property (
        @(posedge clk) $initstate |-> !rst_n
    );

    // A reset cycle drives all registered outputs to their reset values by the next clock.
    check_reset_values: assert property (
        @(posedge clk) !rst_n |=> (state == IDLE && cnt_r == 9'd0 && done_o == 1'b0)
    );

    // State must remain within the defined FSM encodings.
    check_state_encoding: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == IDLE) || (state == LOAD) || (state == YVER) || (state == YHOR) ||
        (state == CVER) || (state == CHOR) || (state == OUTLT) || (state == OUT)
    );

    // Counter must stay within the state-specific terminal count.
    check_counter_bounds: assert property (
        @(posedge clk) disable iff (!rst_n)
        ((state != IDLE)  || (cnt_r == 9'd0))         &&
        ((state != LOAD)  || (cnt_r <= LOAD_CYCLES))  &&
        ((state != YVER)  || (cnt_r <= YVER_CYCLES))  &&
        ((state != YHOR)  || (cnt_r <= YHOR_CYCLES))  &&
        ((state != CVER)  || (cnt_r <= CVER_CYCLES))  &&
        ((state != CHOR)  || (cnt_r <= CHOR_CYCLES))  &&
        ((state != OUTLT) || (cnt_r <= OUTLT_CYCLES)) &&
        ((state != OUT)   || (cnt_r <= OUT_CYCLES))
    );

    // done_o is never high in active processing states.
    check_done_low_outside_idle: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state != IDLE) |-> !done_o
    );

    // done_o can only follow completion of the OUT state.
    check_done_follows_out_completion: assert property (
        @(posedge clk) disable iff (!rst_n)
        done_o |-> $past((state == OUT) && (cnt_r == OUT_CYCLES))
    );

    // done_o is a single-cycle pulse.
    check_done_single_cycle: assert property (
        @(posedge clk) disable iff (!rst_n)
        done_o |=> !done_o
    );

    // IDLE holds when start_i is not asserted.
    check_idle_holds_without_start: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == IDLE && !start_i) |=> (state == IDLE && cnt_r == 9'd0)
    );

    // start_i moves the FSM from IDLE to LOAD.
    check_idle_to_load_on_start: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == IDLE && start_i) |=> (state == LOAD && cnt_r == 9'd0)
    );

    // LOAD increments the counter until its terminal count.
    check_load_counts_until_terminal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == LOAD && cnt_r < LOAD_CYCLES) |=> (state == LOAD && cnt_r == ($past(cnt_r) + 9'd1))
    );

    // LOAD advances to YVER at its terminal count.
    check_load_to_yver_at_terminal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == LOAD && cnt_r == LOAD_CYCLES) |=> (state == YVER && cnt_r == 9'd0)
    );

    // YVER increments the counter until its terminal count.
    check_yver_counts_until_terminal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == YVER && cnt_r < YVER_CYCLES) |=> (state == YVER && cnt_r == ($past(cnt_r) + 9'd1))
    );

    // YVER advances to YHOR at its terminal count.
    check_yver_to_yhor_at_terminal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == YVER && cnt_r == YVER_CYCLES) |=> (state == YHOR && cnt_r == 9'd0)
    );

    // YHOR increments the counter until its terminal count.
    check_yhor_counts_until_terminal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == YHOR && cnt_r < YHOR_CYCLES) |=> (state == YHOR && cnt_r == ($past(cnt_r) + 9'd1))
    );

    // YHOR advances to CVER at its terminal count.
    check_yhor_to_cver_at_terminal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == YHOR && cnt_r == YHOR_CYCLES) |=> (state == CVER && cnt_r == 9'd0)
    );

    // CVER increments the counter until its terminal count.
    check_cver_counts_until_terminal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == CVER && cnt_r < CVER_CYCLES) |=> (state == CVER && cnt_r == ($past(cnt_r) + 9'd1))
    );

    // CVER advances to CHOR at its terminal count.
    check_cver_to_chor_at_terminal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == CVER && cnt_r == CVER_CYCLES) |=> (state == CHOR && cnt_r == 9'd0)
    );

    // CHOR increments the counter until its terminal count.
    check_chor_counts_until_terminal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == CHOR && cnt_r < CHOR_CYCLES) |=> (state == CHOR && cnt_r == ($past(cnt_r) + 9'd1))
    );

    // CHOR advances to OUTLT at its terminal count.
    check_chor_to_outlt_at_terminal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == CHOR && cnt_r == CHOR_CYCLES) |=> (state == OUTLT && cnt_r == 9'd0)
    );

    // OUTLT increments the counter until its terminal count.
    check_outlt_counts_until_terminal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == OUTLT && cnt_r < OUTLT_CYCLES) |=> (state == OUTLT && cnt_r == ($past(cnt_r) + 9'd1))
    );

    // OUTLT advances to OUT at its terminal count.
    check_outlt_to_out_at_terminal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == OUTLT && cnt_r == OUTLT_CYCLES) |=> (state == OUT && cnt_r == 9'd0)
    );

    // OUT increments the counter until its terminal count.
    check_out_counts_until_terminal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == OUT && cnt_r < OUT_CYCLES) |=> (state == OUT && cnt_r == ($past(cnt_r) + 9'd1))
    );

    // OUT returns to IDLE and pulses done_o at completion.
    check_out_to_idle_and_done: assert property (
        @(posedge clk) disable iff (!rst_n)
        (state == OUT && cnt_r == OUT_CYCLES) |=> (state == IDLE && cnt_r == 9'd0 && done_o)
    );

endmodule