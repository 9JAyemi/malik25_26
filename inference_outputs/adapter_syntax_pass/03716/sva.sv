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

    // Reset clears both trace outputs.
    check_reset_clears_outputs: assert property (
        @(posedge clk) !jrst_n |-> (atm == 36'h0) && (dtm == 36'h0)
    );

    // A read cycle captures the address and read data.
    check_read_capture: assert property (
        @(posedge clk) disable iff (!jrst_n)
        cpu_d_read |=> (atm == {21'h0, $past(cpu_d_address)}) &&
                      (dtm == {32'h0, $past(cpu_d_readdata)})
    );

    // A write cycle captures the address and write data.
    check_write_capture: assert property (
        @(posedge clk) disable iff (!jrst_n)
        cpu_d_write |=> (atm == {21'h0, $past(cpu_d_address)}) &&
                       (dtm == {32'h0, $past(cpu_d_writedata)})
    );

    // A wait cycle clears both trace outputs.
    check_wait_clears_outputs: assert property (
        @(posedge clk) disable iff (!jrst_n)
        cpu_d_wait |=> (atm == 36'h0) && (dtm == 36'h0)
    );

    // A read and write cycle prioritize the read capture.
    check_read_over_write_priority: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (cpu_d_read && cpu_d_write) |=> (atm == {21'h0, $past(cpu_d_address)}) &&
                                      (dtm == {32'h0, $past(cpu_d_readdata)})
    );

    // Without a read, write, or wait, the outputs hold their values.
    check_idle_holds_outputs: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (!cpu_d_read && !cpu_d_write && !cpu_d_wait) |=> $stable({atm, dtm})
    );

endmodule