module NIOS_SYSTEMV3_LCD_sva (
    input logic [1:0] address,
    input logic       begintransfer,
    input logic       clk,
    input logic       read,
    input logic       reset_n,
    input logic       write,
    input logic [7:0] writedata,
    input logic       LCD_E,
    input logic       LCD_RS,
    input logic       LCD_RW,
    input logic [7:0] LCD_data
);

    // LCD_RW is the inverse of address[0].
    check_lcd_rw_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
        (LCD_RW == ~address[0])
    );

    // LCD_RS follows address[1].
    check_lcd_rs_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
        (LCD_RS == address[1])
    );

    // LCD_E is low while reset is asserted.
    check_lcd_e_reset_low: assert property (
        @(posedge clk)
        (!reset_n) |-> (LCD_E == 1'b0)
    );

    // LCD_data is zero while reset is asserted.
    check_lcd_data_reset_zero: assert property (
        @(posedge clk)
        (!reset_n) |-> (LCD_data == 8'h00)
    );

    // Any read or write drives LCD_E high on the next cycle.
    check_lcd_e_set_on_access: assert property (
        @(posedge clk) disable iff (!reset_n)
        (read || write) |=> (LCD_E == 1'b1)
    );

    // No read or write drives LCD_E low on the next cycle.
    check_lcd_e_clear_without_access: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!read && !write) |=> (LCD_E == 1'b0)
    );

    // A write captures writedata into LCD_data on the next cycle.
    check_lcd_data_capture_on_write: assert property (
        @(posedge clk) disable iff (!reset_n)
        write |=> (LCD_data == $past(writedata))
    );

    // Without a write, LCD_data holds its previous value.
    check_lcd_data_hold_without_write: assert property (
        @(posedge clk) disable iff (!reset_n)
        !write |=> (LCD_data == $past(LCD_data))
    );

endmodule