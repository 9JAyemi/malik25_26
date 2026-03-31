module limbus_cpu_cpu_nios2_oci_dtrace_sva (
    input logic clk,
    input logic [21:0] cpu_d_address,
    input logic cpu_d_read,
    input logic [31:0] cpu_d_readdata,
    input logic cpu_d_wait,
    input logic cpu_d_write,
    input logic [31:0] cpu_d_writedata,
    input logic jrst_n,
    input logic [15:0] trc_ctrl,
    input logic [35:0] atm,
    input logic [35:0] dtm
);

// Reset drives both outputs to zero.
    check_reset_clears_outputs: assert property (
        @(posedge clk) !jrst_n |-> (atm == 36'h0) && (dtm == 36'h0)
    );

// A read cycle captures the address and read data into atm and dtm.
    check_read_captures_data: assert property (
        @(posedge clk) disable iff (!jrst_n)
        cpu_d_read |=> (atm == {21'h0, $past(cpu_d_address)}) &&
                      (dtm == {32'h0, $past(cpu_d_readdata)})
    );

// A write cycle captures the address and write data into atm and dtm.
    check_write_captures_data: assert property (
        @(posedge clk) disable iff (!jrst_n)
        cpu_d_write |=> (atm == {21'h0, $past(cpu_d_address)}) &&
                       (dtm == {32'h0, $past(cpu_d_writedata)})
    );

// A wait cycle clears both outputs to zero.
    check_wait_clears_outputs: assert property (
        @(posedge clk) disable iff (!jrst_n)
        cpu_d_wait |=> (atm == 36'h0) && (dtm == 36'h0)
    );

// Without any active cycle, the outputs hold their previous values.
    check_idle_holds_outputs: assert property (
        @(posedge clk) disable iff (!jrst_n)
        !(cpu_d_read || cpu_d_write || cpu_d_wait) |=> (atm == $past(atm)) &&
                                                       (dtm == $past(dtm))
    );

// A read cycle has priority over a write cycle when both are asserted.
    check_read_overrides_write: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (cpu_d_read && cpu_d_write) |=> (atm == {21'h0, $past(cpu_d_address)}) &&
                                      (dtm == {32'h0, $past(cpu_d_readdata)})
    );

// A read cycle has priority over a wait cycle when both are asserted.
    check_read_overrides_wait: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (cpu_d_read && cpu_d_wait) |=> (atm == {21'h0, $past(cpu_d_address)}) &&
                                      (dtm == {32'h0, $past(cpu_d_readdata)})
    );

// A write cycle has priority over a wait cycle when both are asserted.
    check_write_overrides_wait: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (cpu_d_write && cpu_d_wait) |=> (atm == {21'h0, $past(cpu_d_address)}) &&
                                       (dtm == {32'h0, $past(cpu_d_writedata)})
    );

endmodule
