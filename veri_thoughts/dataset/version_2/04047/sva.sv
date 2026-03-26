module write_axi_8bit_sva (
    input logic        clock_recovery,
    input logic        clock_50,
    input logic        reset_n,
    input logic [7:0]  data_rec,
    input logic [7:0]  data_stand
);

    // clock_50 is the sequential clock.
    // reset_n is an active-low reset.
    // data_stand conditionally captures data_rec when clock_recovery is high.

    // When reset is sampled low, data_stand is zero by the next clock sample.
    check_reset_clears_data_stand: assert property (
        @(posedge clock_50) !reset_n |=> (data_stand == 8'd0)
    );

    // The registered next value follows the RTL update function.
    check_registered_update_function: assert property (
        @(posedge clock_50) disable iff (!reset_n)
        1'b1 |=> (data_stand == ($past(clock_recovery) ? $past(data_rec) : $past(data_stand)))
    );

    // When clock_recovery is high, data_stand captures data_rec.
    check_capture_when_recovery_high: assert property (
        @(posedge clock_50) disable iff (!reset_n)
        clock_recovery |=> (data_stand == $past(data_rec))
    );

    // When clock_recovery is low, data_stand holds its previous value.
    check_hold_when_recovery_low: assert property (
        @(posedge clock_50) disable iff (!reset_n)
        !clock_recovery |=> (data_stand == $past(data_stand))
    );

endmodule