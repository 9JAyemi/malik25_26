module softusb_timer_sva(
    input logic        usb_clk,
    input logic        usb_rst,
    input logic        io_we,
    input logic [5:0]  io_a,
    input logic [7:0]  io_do,
    input logic [31:0] counter
);

    // Counter is zero after a reset cycle.
    check_counter_zero_after_reset: assert property (
        @(posedge usb_clk) disable iff (usb_rst || $initstate)
        $past(usb_rst) |-> (counter == 32'd0)
    );

    // Output data is zero after a reset cycle.
    check_io_do_zero_after_reset: assert property (
        @(posedge usb_clk) disable iff (usb_rst || $initstate)
        $past(usb_rst) |-> (io_do == 8'd0)
    );

    // A write to any mapped timer address clears the counter.
    check_counter_clears_on_valid_write: assert property (
        @(posedge usb_clk) disable iff (usb_rst || $initstate)
        !$past(usb_rst) &&
        $past(io_we) &&
        (
            ($past(io_a) == 6'h11) ||
            ($past(io_a) == 6'h12) ||
            ($past(io_a) == 6'h13) ||
            ($past(io_a) == 6'h14)
        )
        |-> (counter == 32'd0)
    );

    // All other non-reset cycles increment the counter by one.
    check_counter_increments_without_valid_write: assert property (
        @(posedge usb_clk) disable iff (usb_rst || $initstate)
        !$past(usb_rst) &&
        !(
            $past(io_we) &&
            (
                ($past(io_a) == 6'h11) ||
                ($past(io_a) == 6'h12) ||
                ($past(io_a) == 6'h13) ||
                ($past(io_a) == 6'h14)
            )
        )
        |-> (counter == ($past(counter) + 32'd1))
    );

    // Address 0x11 returns the low byte of the prior counter value.
    check_io_do_addr_11: assert property (
        @(posedge usb_clk) disable iff (usb_rst || $initstate)
        !$past(usb_rst) && ($past(io_a) == 6'h11)
        |-> (io_do == $past(counter[7:0]))
    );

    // Address 0x12 returns the next byte of the prior counter value.
    check_io_do_addr_12: assert property (
        @(posedge usb_clk) disable iff (usb_rst || $initstate)
        !$past(usb_rst) && ($past(io_a) == 6'h12)
        |-> (io_do == $past(counter[15:8]))
    );

    // Address 0x13 returns the third byte of the prior counter value.
    check_io_do_addr_13: assert property (
        @(posedge usb_clk) disable iff (usb_rst || $initstate)
        !$past(usb_rst) && ($past(io_a) == 6'h13)
        |-> (io_do == $past(counter[23:16]))
    );

    // Address 0x14 returns the high byte of the prior counter value.
    check_io_do_addr_14: assert property (
        @(posedge usb_clk) disable iff (usb_rst || $initstate)
        !$past(usb_rst) && ($past(io_a) == 6'h14)
        |-> (io_do == $past(counter[31:24]))
    );

    // Unmapped addresses drive zero on the data output.
    check_io_do_zero_on_unmapped_address: assert property (
        @(posedge usb_clk) disable iff (usb_rst || $initstate)
        !$past(usb_rst) &&
        ($past(io_a) != 6'h11) &&
        ($past(io_a) != 6'h12) &&
        ($past(io_a) != 6'h13) &&
        ($past(io_a) != 6'h14)
        |-> (io_do == 8'd0)
    );

endmodule