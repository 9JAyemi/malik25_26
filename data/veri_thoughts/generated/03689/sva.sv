module sirv_aon_porrst_sva (
    input logic        clk,
    input logic        porrst_n,
    input logic [31:0] counter
);

    // The counter can only hold its value or increment by one each cycle.
    check_counter_hold_or_increment: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> ((counter == $past(counter)) || (counter == ($past(counter) + 32'd1)))
    );

`ifdef FPGA_SOURCE
    // In FPGA builds, POR reset is tied permanently high.
    check_porrst_tied_high_fpga: assert property (
        @(posedge clk) disable iff (1'b0)
        porrst_n == 1'b1
    );
`else
    // While the counter is below 100, the next cycle increments it and keeps POR reset low.
    check_counting_phase_increment_and_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (counter < 32'd100) |=> ((counter == ($past(counter) + 32'd1)) && (porrst_n == 1'b0))
    );

    // Once the counter is 100 or more, the next cycle holds it and drives POR reset high.
    check_saturated_phase_hold_and_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (counter >= 32'd100) |=> ((counter == $past(counter)) && (porrst_n == 1'b1))
    );

    // Transitioning from 99 to 100 still leaves POR reset low in that next cycle.
    check_reaching_100_keeps_porrst_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (counter == 32'd99) |=> ((counter == 32'd100) && (porrst_n == 1'b0))
    );

    // With the counter at 100, the following cycle keeps 100 and deasserts POR reset high.
    check_holding_100_keeps_porrst_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (counter == 32'd100) |=> ((counter == 32'd100) && (porrst_n == 1'b1))
    );
`endif

endmodule