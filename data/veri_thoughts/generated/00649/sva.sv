module ddr3_init_sm_sva (
    input logic rst,
    input logic clk,
    input logic init_done,
    input logic init_start,
    input logic [2:0] state,
    input logic [2:0] next,
    input logic [7:0] init_dly_cnt
);
    // Clock: clk (posedge). Reset: rst (active-high, async). Mixed: sequential FSM + combinational next-state + free-running counter.

    // Mirror DUT encodings for readability
    localparam IDLE        = 3'b000;
    localparam START_CNT   = 3'b001;
    localparam WAITFOR_CNT = 3'b010;
    localparam INIT_DDR    = 3'b011;
    localparam INIT_DONE   = 3'b100;

    ///// Reset behavior /////
    // On reset, state must be IDLE.
    reset_state_to_idle: assert property (
        @(posedge clk) rst |-> (state == IDLE)
    );
    // On reset, init_start must be 0.
    reset_init_start_low: assert property (
        @(posedge clk) rst |-> (init_start == 1'b0)
    );
    // On reset, init_dly_cnt must be 0.
    reset_counter_zero: assert property (
        @(posedge clk) rst |-> (init_dly_cnt == 8'h00)
    );

    ///// Sequential updates /////
    // State register updates from previous next.
    check_state_updates_from_next: assert property (
        @(posedge clk) disable iff (rst) state == $past(next)
    );
    // Counter increments by 1 every cycle when not in reset.
    counter_increments: assert property (
        @(posedge clk) disable iff (rst) init_dly_cnt == ($past(init_dly_cnt) + 8'h01)
    );

    ///// Next-state logic /////
    // From IDLE, next must be START_CNT.
    next_from_idle_is_start: assert property (
        @(posedge clk) disable iff (rst) (state == IDLE) |-> (next == START_CNT)
    );
    // From START_CNT, next must be WAITFOR_CNT.
    next_from_start_is_wait: assert property (
        @(posedge clk) disable iff (rst) (state == START_CNT) |-> (next == WAITFOR_CNT)
    );
    // From WAITFOR_CNT with count hit, next must be INIT_DDR.
    next_from_wait_cnt_hit_is_initddr: assert property (
        @(posedge clk) disable iff (rst) (state == WAITFOR_CNT && init_dly_cnt == 8'h3c) |-> (next == INIT_DDR)
    );
    // From WAITFOR_CNT without count hit, next must be WAITFOR_CNT.
    next_from_wait_cnt_miss_is_wait: assert property (
        @(posedge clk) disable iff (rst) (state == WAITFOR_CNT && init_dly_cnt != 8'h3c) |-> (next == WAITFOR_CNT)
    );
    // From INIT_DDR with init_done asserted, next must be INIT_DONE.
    next_from_initddr_done_is_done: assert property (
        @(posedge clk) disable iff (rst) (state == INIT_DDR && init_done) |-> (next == INIT_DONE)
    );
    // From INIT_DDR with init_done deasserted, next must be INIT_DDR.
    next_from_initddr_notdone_is_initddr: assert property (
        @(posedge clk) disable iff (rst) (state == INIT_DDR && !init_done) |-> (next == INIT_DDR)
    );
    // From INIT_DONE, next must remain INIT_DONE.
    next_from_done_is_done: assert property (
        @(posedge clk) disable iff (rst) (state == INIT_DONE) |-> (next == INIT_DONE)
    );

    ///// Output behavior /////
    // init_start reflects whether next is INIT_DDR.
    init_start_matches_next: assert property (
        @(posedge clk) disable iff (rst) init_start == (next == INIT_DDR)
    );

    ///// One-cycle state transitions /////
    // IDLE -> START_CNT in one cycle.
    state_transition_idle_to_start: assert property (
        @(posedge clk) disable iff (rst) (state == IDLE) |=> (state == START_CNT)
    );
    // START_CNT -> WAITFOR_CNT in one cycle.
    state_transition_start_to_wait: assert property (
        @(posedge clk) disable iff (rst) (state == START_CNT) |=> (state == WAITFOR_CNT)
    );
    // WAITFOR_CNT with count hit -> INIT_DDR in one cycle.
    state_transition_wait_hit_to_initddr: assert property (
        @(posedge clk) disable iff (rst) (state == WAITFOR_CNT && init_dly_cnt == 8'h3c) |=> (state == INIT_DDR)
    );
    // INIT_DDR with init_done -> INIT_DONE in one cycle.
    state_transition_initddr_done_to_done: assert property (
        @(posedge clk) disable iff (rst) (state == INIT_DDR && init_done) |=> (state == INIT_DONE)
    );
endmodule