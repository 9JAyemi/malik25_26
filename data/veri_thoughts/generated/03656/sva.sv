module clk_gen_sva (
    input logic clk100MHz,
    input logic rst,
    input logic clk1MHz,
    input logic clk5KHz,
    input logic clk200Hz,
    input integer count,
    input integer ledmux,
    input integer highspeed
);

    // Formal analysis starts from reset asserted.
    init_reset_assumption: assume property (
        @(posedge clk100MHz) $initstate |-> rst
    );

    // Reset clears all counters and generated clocks.
    check_reset_clears_state: assert property (
        @(posedge clk100MHz)
        rst |-> ((count == 0) && (ledmux == 0) && (highspeed == 0) &&
                 (clk1MHz == 1'b0) && (clk5KHz == 1'b0) && (clk200Hz == 1'b0))
    );

    // count stays within its reachable non-reset range.
    check_count_range: assert property (
        @(posedge clk100MHz) disable iff (rst)
        (count >= 1) && (count <= 250000)
    );

    // ledmux stays within its reachable non-reset range.
    check_ledmux_range: assert property (
        @(posedge clk100MHz) disable iff (rst)
        (ledmux >= 1) && (ledmux <= 5000)
    );

    // highspeed stays within its reachable non-reset range.
    check_highspeed_range: assert property (
        @(posedge clk100MHz) disable iff (rst)
        (highspeed >= 1) && (highspeed <= 50)
    );

    // clk200Hz toggles and count wraps to 1 after reaching 250000.
    check_count_wrap_and_toggle: assert property (
        @(posedge clk100MHz) disable iff (rst)
        (count == 250000) |=> ((count == 1) && (clk200Hz != $past(clk200Hz)))
    );

    // count increments and clk200Hz holds below the wrap point.
    check_count_increment_and_hold: assert property (
        @(posedge clk100MHz) disable iff (rst)
        ((count >= 1) && (count < 250000)) |=> ((count == ($past(count) + 1)) &&
                                                (clk200Hz == $past(clk200Hz)))
    );

    // clk5KHz toggles and ledmux wraps to 1 after reaching 5000.
    check_ledmux_wrap_and_toggle: assert property (
        @(posedge clk100MHz) disable iff (rst)
        (ledmux == 5000) |=> ((ledmux == 1) && (clk5KHz != $past(clk5KHz)))
    );

    // ledmux increments and clk5KHz holds below the wrap point.
    check_ledmux_increment_and_hold: assert property (
        @(posedge clk100MHz) disable iff (rst)
        ((ledmux >= 1) && (ledmux < 5000)) |=> ((ledmux == ($past(ledmux) + 1)) &&
                                                (clk5KHz == $past(clk5KHz)))
    );

    // clk1MHz toggles and highspeed wraps to 1 after reaching 50.
    check_highspeed_wrap_and_toggle: assert property (
        @(posedge clk100MHz) disable iff (rst)
        (highspeed == 50) |=> ((highspeed == 1) && (clk1MHz != $past(clk1MHz)))
    );

    // highspeed increments and clk1MHz holds below the wrap point.
    check_highspeed_increment_and_hold: assert property (
        @(posedge clk100MHz) disable iff (rst)
        ((highspeed >= 1) && (highspeed < 50)) |=> ((highspeed == ($past(highspeed) + 1)) &&
                                                    (clk1MHz == $past(clk1MHz)))
    );

endmodule