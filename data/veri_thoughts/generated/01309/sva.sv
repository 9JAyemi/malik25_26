module hd_data_reader_sva (
    input logic        clk,
    input logic        rst,                 // active-high synchronous reset
    input logic        enable,
    input logic        error,
    input logic        hd_read_from_host,
    input logic [31:0] hd_data_from_host
);
    ///// Reset behavior /////
    // Synchronous reset drives error low by the next cycle.
    reset_clears_error_next: assert property (
        @(posedge clk) rst |=> (error == 1'b0)
    );

    ///// Error clearing on enable rising edge /////
    // Rising edge of enable clears error by the next cycle.
    enable_rise_clears_error: assert property (
        @(posedge clk) disable iff (rst) $rose(enable) |=> (error == 1'b0)
    );

    ///// Error transition rules /////
    // error can only fall due to reset or a rising enable in the previous cycle.
    error_fall_requires_clear_event_prev: assert property (
        @(posedge clk) disable iff (rst)
            $fell(error) |-> ($past(rst,1,1'b0) || ($past(enable,1,1'b0) && !$past(enable,2,1'b0)))
    );

    // error rising requires a host read in the previous cycle.
    error_rise_requires_read_prev: assert property (
        @(posedge clk) disable iff (rst)
            $rose(error) |-> $past(hd_read_from_host,1,1'b0)
    );

    // error rising cannot occur if previous cycle had reset or rising enable.
    error_rise_not_after_prev_reset_or_enrise: assert property (
        @(posedge clk) disable iff (rst)
            $rose(error) |-> (!$past(rst,1,1'b0) && !($past(enable,1,1'b0) && !$past(enable,2,1'b0)))
    );

    // If previous cycle had no read and no rising enable, error must not rise.
    no_error_rise_without_prev_read_or_enrise: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(hd_read_from_host,1,1'b0) && !($past(enable,1,1'b0) && !$past(enable,2,1'b0)))
            |-> !$rose(error)
    );

    // If error was high and previous cycle had no clear event, it remains high.
    error_sticky_without_prev_clear: assert property (
        @(posedge clk) disable iff (rst)
            ($past(error,1,1'b0) && !($past(enable,1,1'b0) && !$past(enable,2,1'b0)))
            |-> (error == 1'b1)
    );

    // With no read and no rising enable in the previous cycle, error is stable.
    error_stable_without_prev_activity: assert property (
        @(posedge clk) disable iff (rst)
            (!$past(hd_read_from_host,1,1'b0) && !($past(enable,1,1'b0) && !$past(enable,2,1'b0)))
            |-> $stable(error)
    );

endmodule