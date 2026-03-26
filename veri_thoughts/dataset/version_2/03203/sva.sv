module uart_rx_assertions #
(
    parameter DATA_WIDTH = 8
)
(
    input  logic                  clk,
    input  logic                  rst,
    input  logic [DATA_WIDTH-1:0] output_axis_tdata,
    input  logic                  output_axis_tvalid,
    input  logic                  output_axis_tready,
    input  logic                  rxd,
    input  logic                  busy,
    input  logic                  overrun_error,
    input  logic                  frame_error,
    input  logic [15:0]           prescale
);

    // Reset clears the observable outputs and status flags.
    check_reset_clears_outputs: assert property (
        @(posedge clk)
        rst |-> (!output_axis_tvalid && !busy && !overrun_error && !frame_error && (output_axis_tdata == '0))
    );

    // Overrun and frame error are never asserted together.
    check_error_mutex: assert property (
        @(posedge clk) disable iff (rst)
        !(overrun_error && frame_error)
    );

    // An overrun indication always leaves the output valid asserted.
    check_overrun_implies_valid: assert property (
        @(posedge clk) disable iff (rst)
        overrun_error |-> output_axis_tvalid
    );

    // An overrun indication occurs while the receiver is still busy.
    check_overrun_implies_busy: assert property (
        @(posedge clk) disable iff (rst)
        overrun_error |-> busy
    );

    // Overrun can only occur if output valid was already set in the prior cycle.
    check_overrun_requires_prior_valid: assert property (
        @(posedge clk) disable iff (rst)
        overrun_error |-> $past(output_axis_tvalid)
    );

    // A frame error is reported while the receiver is still busy.
    check_frame_error_implies_busy: assert property (
        @(posedge clk) disable iff (rst)
        frame_error |-> busy
    );

    // Valid stays asserted while backpressured.
    check_valid_holds_under_backpressure: assert property (
        @(posedge clk) disable iff (rst)
        (output_axis_tvalid && !output_axis_tready) |=> output_axis_tvalid
    );

    // Valid can only fall after a ready/valid handshake.
    check_valid_fall_requires_handshake: assert property (
        @(posedge clk) disable iff (rst)
        $fell(output_axis_tvalid) |-> $past(output_axis_tvalid && output_axis_tready)
    );

    // Overrun error is a single-cycle pulse.
    check_overrun_single_cycle: assert property (
        @(posedge clk) disable iff (rst)
        overrun_error |=> !overrun_error
    );

    // Frame error is a single-cycle pulse.
    check_frame_error_single_cycle: assert property (
        @(posedge clk) disable iff (rst)
        frame_error |=> !frame_error
    );

    // Output data only changes when the output is valid.
    check_data_change_implies_valid: assert property (
        @(posedge clk) disable iff (rst)
        $changed(output_axis_tdata) |-> output_axis_tvalid
    );

    // Output data changes only while the receiver is busy.
    check_data_change_while_busy: assert property (
        @(posedge clk) disable iff (rst)
        $changed(output_axis_tdata) |-> busy
    );

    // A new assertion of valid happens while the receiver is busy.
    check_valid_rise_while_busy: assert property (
        @(posedge clk) disable iff (rst)
        $rose(output_axis_tvalid) |-> busy
    );

endmodule