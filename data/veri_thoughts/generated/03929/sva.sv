module sdram_init_sva #(
    parameter INIT_CNT = 16'h4000
) (
    input logic        sdram_clk,
    input logic        sdram_rst_,
    input logic        PAA,
    input logic        SET_MODE,
    input logic [15:0] init_counter,
    input logic        init_counter_done
);

    localparam [15:0] INIT_CNT_MINUS_ONE = INIT_CNT - 16'd1;

    // init_counter_done matches the terminal-count compare.
    check_done_flag_definition: assert property (
        @(posedge sdram_clk) disable iff (!sdram_rst_)
        (init_counter_done == (init_counter == INIT_CNT))
    );

    // A reset clock clears the counter to zero.
    check_counter_resets_to_zero: assert property (
        @(posedge sdram_clk)
        (!sdram_rst_) |=> (init_counter == 16'h0000)
    );

    // The counter increments by one while not done.
    check_counter_increments_before_done: assert property (
        @(posedge sdram_clk) disable iff (!sdram_rst_)
        (!init_counter_done) |=> (init_counter == ($past(init_counter) + 16'd1))
    );

    // The counter stops changing once done is high.
    check_counter_holds_when_done: assert property (
        @(posedge sdram_clk) disable iff (!sdram_rst_)
        init_counter_done |=> (init_counter == $past(init_counter))
    );

    // INIT_CNT-1 advances to the done condition on the next cycle.
    check_done_after_penultimate_count: assert property (
        @(posedge sdram_clk) disable iff (!sdram_rst_)
        (init_counter == INIT_CNT_MINUS_ONE) |=> init_counter_done
    );

    // PAA stays low when done was low on the prior clock.
    check_paa_low_after_not_done: assert property (
        @(posedge sdram_clk) disable iff (!sdram_rst_)
        (!init_counter_done) |=> (!PAA)
    );

    // PAA goes high when done was high on the prior clock.
    check_paa_high_after_done: assert property (
        @(posedge sdram_clk) disable iff (!sdram_rst_)
        init_counter_done |=> PAA
    );

    // SET_MODE is driven high after every clock edge.
    check_set_mode_driven_high: assert property (
        @(posedge sdram_clk)
        1'b1 |=> (SET_MODE == 1'b1)
    );

endmodule

bind sdram_init sdram_init_sva #(
    .INIT_CNT(INIT_CNT)
) sdram_init_sva_inst (
    .sdram_clk(sdram_clk),
    .sdram_rst_(sdram_rst_),
    .PAA(PAA),
    .SET_MODE(SET_MODE),
    .init_counter(init_counter),
    .init_counter_done(init_counter_done)
);