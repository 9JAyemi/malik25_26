module soc_system_jtag_uart_sim_scfifo_w_sva (
    input logic        clk,
    input logic [7:0]  fifo_wdata,
    input logic        fifo_wr,
    input logic        fifo_FF,
    input logic [7:0]  r_dat,
    input logic        wfifo_empty,
    input logic [5:0]  wfifo_used
);

    // Read data is tied to zero.
    check_r_dat_zero: assert property (
        @(posedge clk) r_dat == 8'h00
    );

    // Full flag is tied low.
    check_fifo_ff_zero: assert property (
        @(posedge clk) fifo_FF == 1'b0
    );

    // Empty implies the visible used count is zero.
    check_empty_implies_zero_used: assert property (
        @(posedge clk) wfifo_empty |-> (wfifo_used == 6'd0)
    );

    // Without a write, the used count holds its value.
    check_used_holds_without_write: assert property (
        @(posedge clk) !fifo_wr |=> (wfifo_used == $past(wfifo_used))
    );

    // A write increments the used count modulo 64.
    check_used_increments_on_write: assert property (
        @(posedge clk) fifo_wr |=> (wfifo_used == ($past(wfifo_used) + 6'd1))
    );

    // Once non-empty, it stays non-empty.
    check_nonempty_sticky: assert property (
        @(posedge clk) !wfifo_empty |=> !wfifo_empty
    );

    // Empty remains asserted if no write occurs.
    check_empty_holds_without_write: assert property (
        @(posedge clk) (wfifo_empty && !fifo_wr) |=> wfifo_empty
    );

    // A write from empty makes the FIFO non-empty.
    check_write_from_empty_clears_empty: assert property (
        @(posedge clk) (wfifo_empty && fifo_wr) |=> !wfifo_empty
    );

    // A write from empty sets the used count to one.
    check_write_from_empty_sets_used_one: assert property (
        @(posedge clk) (wfifo_empty && fifo_wr) |=> (wfifo_used == 6'd1)
    );

endmodule