module limbus_cpu_cpu_nios2_oci_dtrace_sva (
    input logic        clk,
    input logic        jrst_n,
    input logic [21:0] cpu_d_address,
    input logic        cpu_d_read,
    input logic        cpu_d_write,
    input logic        cpu_d_wait,
    input logic [35:0] atm,
    input logic [35:0] dtm
);

    // Reset clears both trace outputs.
    check_reset_clears_trace_outputs: assert property (
        @(posedge clk) !jrst_n |-> (atm == 36'h0) && (dtm == 36'h0)
    );

    // A read captures the address and read data into the outputs.
    check_read_captures_trace_outputs: assert property (
        @(posedge clk) disable iff (!jrst_n)
        cpu_d_read |=> (atm == {21'h0, $past(cpu_d_address)}) &&
                      (dtm == {32'h0, $past(cpu_d_readdata)})
    );

    // A write captures the address and write data into the outputs.
    check_write_captures_trace_outputs: assert property (
        @(posedge clk) disable iff (!jrst_n)
        cpu_d_write |=> (atm == {21'h0, $past(cpu_d_address)}) &&
                       (dtm == {32'h0, $past(cpu_d_writedata)})
    );

    // A wait clears both trace outputs.
    check_wait_clears_trace_outputs: assert property (
        @(posedge clk) disable iff (!jrst_n)
        cpu_d_wait |=> (atm == 36'h0) && (dtm == 36'h0)
    );

    // With no active request, the outputs hold their previous values.
    check_idle_holds_trace_outputs: assert property (
        @(posedge clk) disable iff (!jrst_n)
        !(cpu_d_read || cpu_d_write || cpu_d_wait) |=> (atm == $past(atm)) &&
                                                       (dtm == $past(dtm))
    );

endmodule