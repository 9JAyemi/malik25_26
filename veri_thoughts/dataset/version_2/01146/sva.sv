module rippleCounter_sva (
    input logic clk,
    input logic rst_n,
    input logic [3:0] out
);

    ///// Reset behavior /////
    // While reset is asserted, out is 0 at each clock.
    check_reset_zero: assert property (
        @(posedge clk) (!rst_n |-> (out == 4'd0))
    );

    ///// Counting behavior /////
    // When running and previous out != 15, out increments by 1.
    check_increment_no_wrap: assert property (
        @(posedge clk) disable iff (!rst_n)
            ($past(rst_n) && ($past(out) != 4'd15)) |-> (out == $past(out) + 4'd1)
    );

    // When running and previous out == 15, out wraps to 0.
    check_wrap_15_to_0: assert property (
        @(posedge clk) disable iff (!rst_n)
            ($past(rst_n) && ($past(out) == 4'd15)) |-> (out == 4'd0)
    );

    // When running, out changes every cycle (no hold).
    check_out_changes_each_cycle: assert property (
        @(posedge clk) disable iff (!rst_n)
            $past(rst_n) |-> (out != $past(out))
    );

    // When out of reset for 16 consecutive cycles, state repeats every 16.
    check_periodicity_16: assert property (
        @(posedge clk) disable iff (!rst_n)
            ( rst_n && $past(rst_n,1) && $past(rst_n,2) && $past(rst_n,3) && $past(rst_n,4)
              && $past(rst_n,5) && $past(rst_n,6) && $past(rst_n,7) && $past(rst_n,8)
              && $past(rst_n,9) && $past(rst_n,10) && $past(rst_n,11) && $past(rst_n,12)
              && $past(rst_n,13) && $past(rst_n,14) && $past(rst_n,15) ) |-> (out == $past(out,16))
    );

    ///// Reset edge effects /////
    // One cycle after a reset assertion, out is 0.
    check_zero_next_after_reset_assert: assert property (
        @(posedge clk) $fell(rst_n) |=> (out == 4'd0)
    );

    // On the clock where reset deasserts, out is still 0.
    check_zero_at_reset_release_edge: assert property (
        @(posedge clk) disable iff (!rst_n)
            $rose(rst_n) |-> (out == 4'd0)
    );

    // One cycle after reset deasserts, out becomes 1.
    check_one_after_reset_release: assert property (
        @(posedge clk) disable iff (!rst_n)
            $rose(rst_n) |=> (out == 4'd1)
    );

    ///// Additional invariants /////
    // When running, out == 0 only if previous out was 15.
    check_zero_only_after_wrap: assert property (
        @(posedge clk) disable iff (!rst_n)
            ($past(rst_n) && (out == 4'd0)) |-> ($past(out) == 4'd15)
    );

    // When running, LSB toggles every cycle.
    check_lsb_toggles: assert property (
        @(posedge clk) disable iff (!rst_n)
            $past(rst_n) |-> (out[0] == ~$past(out[0]))
    );

endmodule