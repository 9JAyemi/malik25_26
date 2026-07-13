module NIOS_SYSTEMV3_JTAG_UART_sim_scfifo_r_sva (
    input  logic        clk,
    input  logic        fifo_rd,
    input  logic        rst_n,
    input  logic        fifo_EF,
    input  logic [7:0]  fifo_rdata,
    input  logic        rfifo_full,
    input  logic [5:0]  rfifo_used
);
    // Clock: clk; Reset: rst_n active-low async. Logic: sequential with combinational status.
    // Status outputs reflect bytes_left; new_rom/num_bytes are tied to 0; fifo_rdata is tied to 0.

    // On reset assertion, outputs are driven to known values.
    reset_outputs_known_values: assert property (
        @(posedge clk) !rst_n |-> (fifo_EF == 1'b1) && (rfifo_full == 1'b0) && (rfifo_used == 6'b0) && (fifo_rdata == 8'h00)
    );

    // fifo_rdata is always 0.
    check_rdata_const_zero: assert property (
        @(posedge clk) disable iff (!rst_n) (fifo_rdata == 8'h00)
    );

    // FULL implies not EMPTY.
    check_full_implies_not_empty: assert property (
        @(posedge clk) disable iff (!rst_n) rfifo_full |-> (fifo_EF == 1'b0)
    );

    // EMPTY implies not FULL.
    check_empty_implies_not_full: assert property (
        @(posedge clk) disable iff (!rst_n) fifo_EF |-> (rfifo_full == 1'b0)
    );

    // FULL forces rfifo_used to 0.
    check_full_implies_used_zero: assert property (
        @(posedge clk) disable iff (!rst_n) rfifo_full |-> (rfifo_used == 6'b0)
    );

    // EMPTY forces rfifo_used to 0.
    check_empty_implies_used_zero: assert property (
        @(posedge clk) disable iff (!rst_n) fifo_EF |-> (rfifo_used == 6'b0)
    );

    // FULL and EMPTY are mutually exclusive.
    check_full_empty_mutex: assert property (
        @(posedge clk) disable iff (!rst_n) !(rfifo_full && fifo_EF)
    );

    // If no read in the previous cycle, status outputs hold their values.
    check_status_stable_if_no_prev_read: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(fifo_rd) == 1'b0) |-> (fifo_EF == $past(fifo_EF)) && (rfifo_full == $past(rfifo_full)) && (rfifo_used == $past(rfifo_used))
    );

    // Reading while EMPTY causes next cycle to be not EMPTY and FULL with used==0 (wrap-underflow).
    check_empty_read_wraps_to_full: assert property (
        @(posedge clk) disable iff (!rst_n) $past(fifo_EF && fifo_rd) |-> (fifo_EF == 1'b0) && (rfifo_full == 1'b1) && (rfifo_used == 6'b0)
    );

    // Reading while previously FULL keeps rfifo_used at 0 in the next cycle.
    check_full_read_keeps_used_zero: assert property (
        @(posedge clk) disable iff (!rst_n) $past(rfifo_full && fifo_rd) |-> (rfifo_used == 6'b0)
    );

endmodule