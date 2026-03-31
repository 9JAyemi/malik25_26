module reset_sync_sva (
    input logic reset_n,
    input logic clk,
    input logic [0:0] reset_n_sync
);

// reset_n_sync is LOW on the first clock after reset_n goes LOW.
    check_sync_low_after_reset_fall: assert property (
        @(posedge clk) !reset_n |=> (reset_n_sync == 1'b0)
    );

// reset_n_sync is HIGH on the first clock after reset_n goes HIGH.
    check_sync_high_after_reset_rise: assert property (
        @(posedge clk) disable iff (!reset_n) $rose(reset_n) |=> (reset_n_sync == 1'b1)
    );

// A reset cycle (fall then rise) leaves reset_n_sync LOW on the second clock.
    check_sync_low_after_reset_cycle: assert property (
        @(posedge clk) (!reset_n ##1 reset_n) |=> (reset_n_sync == 1'b0)
    );

// A reset cycle (fall then rise) leaves reset_n_sync LOW on the second clock.
    check_sync_low_after_reset_cycle: assert property (
        @(posedge clk) (!reset_n ##1 reset_n) |=> (reset_n_sync == 1'b0)
    );

// A reset cycle (fall then rise) leaves reset_n_sync LOW on the second clock.
    check_sync_low_after_reset_cycle: assert property (
        @(posedge clk) (!reset_n ##1 reset_n) |=> (reset_n_sync == 1'b0)
    );

// A reset cycle (fall then rise) leaves reset_n_sync LOW on the second clock.
    check_sync_low_after_reset_cycle: assert property (
        @(posedge clk) (!reset_n ##1 reset_n) |=> (reset_n_sync == 1'b0)
    );

// A reset cycle (fall then rise) leaves reset_n_sync LOW on the second clock.
    check_sync_low_after_reset_cycle: assert property (
        @(posedge clk) (!reset_n ##1 reset_n) |=> (reset_n_sync == 1'b0)
    );

// A reset cycle (fall then rise) leaves reset_n_sync LOW on the second clock.
    check_sync_low_after_reset_cycle: assert property (
        @(posedge clk) (!reset_n ##1 reset_n) |=> (reset_n_sync == 1'b0)
    );

// A reset cycle (fall then rise) leaves reset_n_sync LOW on the second clock.
    check_sync_low_after_reset_cycle: assert property (
        @(posedge clk) (!reset_n ##1 reset_n) |=> (reset_n_sync == 1'b0)
    );

// A reset cycle (fall then rise) leaves reset_n_sync LOW on the second clock.
    check_sync_low_after_reset_cycle: assert property (
        @(posedge clk) (!reset_n ##1 reset_n) |=> (reset_n_sync == 1'b0)
    );

endmodule
