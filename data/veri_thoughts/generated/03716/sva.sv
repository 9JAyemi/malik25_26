module limbus_cpu_cpu_nios2_oci_dtrace_sva (
    input logic        clk,
    input logic [21:0] cpu_d_address,
    input logic        cpu_d_read,
    input logic [31:0] cpu_d_readdata,
    input logic        cpu_d_wait,
    input logic        cpu_d_write,
    input logic [31:0] cpu_d_writedata,
    input logic        jrst_n,
    input logic [15:0] trc_ctrl,
    input logic [35:0] atm,
    input logic [35:0] dtm
);

    // Reset forces both trace outputs to zero.
    check_reset_clears_outputs: assert property (
        @(posedge clk)
        !jrst_n |-> (atm == 36'b0 && dtm == 36'b0)
    );

    // A read captures the address and read data.
    check_read_captures_addr_and_data: assert property (
        @(posedge clk) disable iff (!jrst_n)
        cpu_d_read |=> (atm == {14'b0, $past(cpu_d_address)} &&
                        dtm == {4'b0,  $past(cpu_d_readdata)})
    );

    // A write captures the address and write data when no read is present.
    check_write_captures_addr_and_data: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (!cpu_d_read && cpu_d_write) |=> (atm == {14'b0, $past(cpu_d_address)} &&
                                          dtm == {4'b0,  $past(cpu_d_writedata)})
    );

    // A wait with no read or write clears both outputs.
    check_wait_clears_outputs: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (!cpu_d_read && !cpu_d_write && cpu_d_wait) |=> (atm == 36'b0 && dtm == 36'b0)
    );

    // With no control activity, both outputs hold their previous values.
    check_idle_holds_outputs: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (!cpu_d_read && !cpu_d_write && !cpu_d_wait) |=> (atm == $past(atm) && dtm == $past(dtm))
    );

    // Read has priority over write and wait.
    check_read_has_priority_over_write_or_wait: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (cpu_d_read && (cpu_d_write || cpu_d_wait)) |=> (atm == {14'b0, $past(cpu_d_address)} &&
                                                         dtm == {4'b0,  $past(cpu_d_readdata)})
    );

    // Write has priority over wait when no read is present.
    check_write_has_priority_over_wait: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (!cpu_d_read && cpu_d_write && cpu_d_wait) |=> (atm == {14'b0, $past(cpu_d_address)} &&
                                                        dtm == {4'b0,  $past(cpu_d_writedata)})
    );

endmodule