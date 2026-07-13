module lcd_driver_sva (
    input logic        clk,
    input logic [7:0]  data,
    input logic [1:0]  ctrl,
    input logic [15:0] display
);

    // ctrl=00 places data in the low byte.
    check_display_beginning_of_line: assert property (
        @(posedge clk) (ctrl == 2'b00) |-> (display == {8'b0, data})
    );

    // ctrl=01 places data in the high byte.
    check_display_end_of_line: assert property (
        @(posedge clk) (ctrl == 2'b01) |-> (display == {data, 8'b0})
    );

    // ctrl=10 centers data with zero padding.
    check_display_centered: assert property (
        @(posedge clk) (ctrl == 2'b10) |-> (display == {4'b0, data, 4'b0})
    );

    // ctrl=11 clears the display.
    check_display_clear: assert property (
        @(posedge clk) (ctrl == 2'b11) |-> (display == 16'h0000)
    );

endmodule