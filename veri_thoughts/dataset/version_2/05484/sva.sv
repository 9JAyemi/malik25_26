module ctr_fsm_sva (
    input logic       clk,
    input logic       ar,
    input logic       start,
    input logic       stop,
    input logic       ctr_en,
    input logic       ctr_ar,
    input logic [1:0] state
);

    localparam [1:0] IDLE    = 2'b00;
    localparam [1:0] PRERUN  = 2'b01;
    localparam [1:0] RUN     = 2'b10;
    localparam [1:0] STOPPED = 2'b11;

    localparam start_assert = 1'b1;
    localparam stop_assert  = 1'b0;

    // Active-low reset forces IDLE and idle outputs.
    check_reset_to_idle: assert property (
        @(posedge clk) !ar |-> (state == IDLE) && (ctr_en == 1'b0) && (ctr_ar == 1'b0)
    );

    // ctr_en is high only in RUN.
    check_ctr_en_decode: assert property (
        @(posedge clk) disable iff (!ar) ctr_en == (state == RUN)
    );

    // ctr_ar is low only in IDLE and PRERUN.
    check_ctr_ar_decode: assert property (
        @(posedge clk) disable iff (!ar) ctr_ar == ~((state == PRERUN) || (state == IDLE))
    );

    // IDLE moves to PRERUN when start is asserted.
    check_idle_to_prerun_on_start: assert property (
        @(posedge clk) disable iff (!ar) (state == IDLE && start == start_assert) |=> (state == PRERUN)
    );

    // IDLE stays in IDLE when start is not asserted.
    check_idle_stays_idle_without_start: assert property (
        @(posedge clk) disable iff (!ar) (state == IDLE && start != start_assert) |=> (state == IDLE)
    );

    // PRERUN moves to STOPPED when stop is asserted.
    check_prerun_to_stopped_on_stop: assert property (
        @(posedge clk) disable iff (!ar) (state == PRERUN && stop == stop_assert) |=> (state == STOPPED)
    );

    // PRERUN moves to RUN when stop is not asserted.
    check_prerun_to_run_without_stop: assert property (
        @(posedge clk) disable iff (!ar) (state == PRERUN && stop != stop_assert) |=> (state == RUN)
    );

    // RUN moves to STOPPED when stop is asserted.
    check_run_to_stopped_on_stop: assert property (
        @(posedge clk) disable iff (!ar) (state == RUN && stop == stop_assert) |=> (state == STOPPED)
    );

    // RUN stays in RUN when stop is not asserted.
    check_run_stays_run_without_stop: assert property (
        @(posedge clk) disable iff (!ar) (state == RUN && stop != stop_assert) |=> (state == RUN)
    );

    // STOPPED returns to IDLE when start is deasserted.
    check_stopped_to_idle_on_start_deassert: assert property (
        @(posedge clk) disable iff (!ar) (state == STOPPED && start != start_assert) |=> (state == IDLE)
    );

    // STOPPED stays in STOPPED while start is asserted.
    check_stopped_stays_stopped_on_start_assert: assert property (
        @(posedge clk) disable iff (!ar) (state == STOPPED && start == start_assert) |=> (state == STOPPED)
    );

endmodule