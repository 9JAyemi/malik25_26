module baud_rate_generator_sva (
    input logic clk,
    input logic rst_n,
    input logic bps_start,
    input logic clk_baud,
    // Internal DUT signals (from RTL)
    input logic [31:0] counter,
    input logic toggle
);
    // Mirror DUT parameters to compute threshold used in RTL
    parameter int BAUD_RATE = 9600;
    parameter int freq = 16000000;
    localparam int THRESH = freq / (BAUD_RATE * 2);

    ///// Reset behavior /////
    // While reset is asserted, counter and toggle are 0 and clk_baud is LOW.
    reset_drive_low: assert property (
        @(posedge clk) !rst_n |-> (counter == 32'd0) && (toggle == 1'b0) && (clk_baud == 1'b0)
    );

    // On the cycle reset deasserts, state remains cleared (toggle=0, counter=0, clk_baud=0).
    reset_release_clear: assert property (
        @(posedge clk) $rose(rst_n) |-> (counter == 32'd0) && (toggle == 1'b0) && (clk_baud == 1'b0)
    );

    ///// Output connectivity /////
    // clk_baud must always mirror toggle (continuous assign).
    check_clk_baud_mirrors_toggle: assert property (
        @(posedge clk) disable iff (!rst_n) (clk_baud === toggle)
    );

    ///// Functional behavior /////
    // When bps_start is HIGH and counter equals THRESH, next cycle toggle flips and counter resets to 0.
    toggle_on_threshold: assert property (
        @(posedge clk) disable iff (!rst_n)
            (bps_start && (counter == THRESH)) |=> (toggle == ~$past(toggle)) && (counter == 32'd0)
    );

    // When bps_start is HIGH and counter is not THRESH, next cycle counter increments and toggle holds.
    count_when_running: assert property (
        @(posedge clk) disable iff (!rst_n)
            (bps_start && (counter != THRESH)) |=> (counter == $past(counter) + 32'd1) && (toggle == $past(toggle))
    );

    // When bps_start is LOW, next cycle counter and toggle hold their values (no counting).
    hold_when_stopped: assert property (
        @(posedge clk) disable iff (!rst_n)
            (!bps_start) |=> (counter == $past(counter)) && (toggle == $past(toggle)) && (clk_baud == $past(clk_baud))
    );

endmodule