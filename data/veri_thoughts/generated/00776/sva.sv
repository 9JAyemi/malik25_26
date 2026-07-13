module write_axi_9bit_sva (
    input  logic        clock_recovery,
    input  logic        clock_50,
    input  logic        reset_n,
    input  logic [8:0]  data_rec,
    input  logic [8:0]  data_stand
);

    ///// Reset behavior /////
    // While reset_n is LOW, data_stand must be 0.
    reset_forces_zero: assert property (
        @(posedge clock_50) !reset_n |-> (data_stand == 9'd0)
    );

    ///// Sequential load/hold behavior /////
    // If not in reset last cycle and enable was 1, load previous data_rec.
    load_on_enable_prev_cycle: assert property (
        @(posedge clock_50) disable iff (!reset_n)
            ($past(reset_n) && $past(clock_recovery)) |-> (data_stand == $past(data_rec))
    );

    // If not in reset last cycle and enable was 0, hold previous value.
    hold_on_disable_prev_cycle: assert property (
        @(posedge clock_50) disable iff (!reset_n)
            ($past(reset_n) && !$past(clock_recovery)) |-> (data_stand == $past(data_stand))
    );

    // Next value is the mux of previous values based on previous enable.
    next_value_matches_prev_mux: assert property (
        @(posedge clock_50) disable iff (!reset_n)
            $past(reset_n) |-> (data_stand == ($past(clock_recovery) ? $past(data_rec) : $past(data_stand)))
    );

    // With enable LOW for two consecutive prior cycles (and not in reset two cycles ago), value matches from two cycles ago.
    hold_across_two_disable_cycles: assert property (
        @(posedge clock_50) disable iff (!reset_n)
            ($past(reset_n,2) && !$past(clock_recovery,1) && !$past(clock_recovery,2)) |-> (data_stand == $past(data_stand,2))
    );

endmodule