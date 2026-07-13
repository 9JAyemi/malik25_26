module omsp_sync_reset_sva (
    input logic       rst_s,
    input logic       clk,
    input logic       rst_a,
    input logic [1:0] data_sync
);

    // Out of reset, rst_s must reflect the MSB of the synchronizer register.
    check_output_matches_sync_msb: assert property (
        @(posedge clk) disable iff (rst_a) (rst_s == data_sync[1])
    );

    // A sampled asserted reset must produce 2'b11 by the next clock sample.
    check_reset_loads_all_ones_next_cycle: assert property (
        @(posedge clk) rst_a |=> (data_sync == 2'b11)
    );

    // A sampled asserted reset must keep the synchronized reset output high next cycle.
    check_reset_drives_output_high_next_cycle: assert property (
        @(posedge clk) rst_a |=> (rst_s == 1'b1)
    );

    // If reset is sampled high on two consecutive clocks, the state stays at 2'b11.
    check_reset_hold_keeps_all_ones: assert property (
        @(posedge clk) (rst_a ##1 rst_a) |-> (data_sync == 2'b11)
    );

    // If reset is sampled high on two consecutive clocks, the output stays high.
    check_reset_hold_keeps_output_high: assert property (
        @(posedge clk) (rst_a ##1 rst_a) |-> (rst_s == 1'b1)
    );

    // On the sampled release cycle, the synchronizer still holds 2'b11 before shifting.
    check_release_cycle_still_holds_ones: assert property (
        @(posedge clk) (rst_a ##1 !rst_a) |-> (data_sync == 2'b11)
    );

    // On the sampled release cycle, the synchronized reset output is still high.
    check_release_cycle_output_still_high: assert property (
        @(posedge clk) (rst_a ##1 !rst_a) |-> (rst_s == 1'b1)
    );

endmodule