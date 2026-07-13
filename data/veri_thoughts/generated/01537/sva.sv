module niosII_system_nios2_qsys_0_nios2_oci_dbrk_sva (
    input logic [31:0] E_st_data,
    input logic [31:0] av_ld_data_aligned_filtered,
    input logic clk,
    input logic [24:0] d_address,
    input logic d_read,
    input logic d_waitrequest,
    input logic d_write,
    input logic debugack,
    input logic reset_n,

    input logic [24:0] cpu_d_address,
    input logic cpu_d_read,
    input logic [31:0] cpu_d_readdata,
    input logic cpu_d_wait,
    input logic cpu_d_write,
    input logic [31:0] cpu_d_writedata,
    input logic dbrk_break,
    input logic dbrk_goto0,
    input logic dbrk_goto1,
    input logic dbrk_traceme,
    input logic dbrk_traceoff,
    input logic dbrk_traceon,
    input logic dbrk_trigout
);
    // On reset low, all outputs drive zero.
    reset_outputs_zero: assert property (
        @(posedge clk) !reset_n |-> 
            (cpu_d_writedata == 32'd0) &&
            (cpu_d_address == 25'd0) &&
            (cpu_d_read == 1'b0) &&
            (cpu_d_readdata == 32'd0) &&
            (cpu_d_wait == 1'b0) &&
            (cpu_d_write == 1'b0) &&
            (dbrk_break == 1'b0) &&
            (dbrk_goto0 == 1'b0) &&
            (dbrk_goto1 == 1'b0) &&
            (dbrk_traceme == 1'b0) &&
            (dbrk_traceoff == 1'b0) &&
            (dbrk_traceon == 1'b0) &&
            (dbrk_trigout == 1'b0)
    );

    // cpu_d_writedata updates from E_st_data when d_write else from av_ld_data_aligned_filtered.
    check_writedata_update: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) |-> (cpu_d_writedata == $past(d_write ? E_st_data : av_ld_data_aligned_filtered))
    );

    // cpu_d_address updates from d_address when d_write else zero.
    check_address_update: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) |-> (cpu_d_address == $past(d_write ? d_address : 25'd0))
    );

    // cpu_d_read deasserts when d_write else follows d_read.
    check_read_update: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) |-> (cpu_d_read == $past(d_write ? 1'b0 : d_read))
    );

    // cpu_d_readdata captures av_ld_data_aligned_filtered when d_read else zero.
    check_readdata_update: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) |-> (cpu_d_readdata == $past(d_read ? av_ld_data_aligned_filtered : 32'd0))
    );

    // cpu_d_wait follows d_waitrequest with one-cycle latency.
    check_wait_update: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) |-> (cpu_d_wait == $past(d_waitrequest))
    );

    // cpu_d_write mirrors d_write with one-cycle latency.
    check_write_update: assert property (
        @(posedge clk) disable iff (!reset_n)
            $past(reset_n) |-> (cpu_d_write == $past(d_write))
    );

    // When writing, no read is asserted in the same cycle.
    check_no_read_when_write: assert property (
        @(posedge clk) disable iff (!reset_n)
            cpu_d_write |-> (cpu_d_read == 1'b0)
    );

    // When not writing, address is zero.
    check_address_zero_when_not_write: assert property (
        @(posedge clk) disable iff (!reset_n)
            !cpu_d_write |-> (cpu_d_address == 25'd0)
    );

    // When writing, address matches prior d_address.
    check_address_matches_when_write: assert property (
        @(posedge clk) disable iff (!reset_n)
            (cpu_d_write && $past(reset_n)) |-> (cpu_d_address == $past(d_address))
    );

    // When writing, writedata matches prior E_st_data.
    check_writedata_matches_when_write: assert property (
        @(posedge clk) disable iff (!reset_n)
            (cpu_d_write && $past(reset_n)) |-> (cpu_d_writedata == $past(E_st_data))
    );

    // When not writing, writedata matches prior av_ld_data_aligned_filtered.
    check_writedata_matches_when_not_write: assert property (
        @(posedge clk) disable iff (!reset_n)
            (!cpu_d_write && $past(reset_n)) |-> (cpu_d_writedata == $past(av_ld_data_aligned_filtered))
    );

    // If a read occurred last cycle, readdata matches prior av_ld_data_aligned_filtered.
    check_readdata_when_read: assert property (
        @(posedge clk) disable iff (!reset_n)
            ($past(reset_n) && $past(d_read)) |-> (cpu_d_readdata == $past(av_ld_data_aligned_filtered))
    );

    // If no read occurred last cycle, readdata is zero.
    check_readdata_zero_when_no_read: assert property (
        @(posedge clk) disable iff (!reset_n)
            ($past(reset_n) && !$past(d_read)) |-> (cpu_d_readdata == 32'd0)
    );

    // dbrk_break toggles when debugack is low in the previous cycle.
    check_dbrk_break_toggle_on_ack_low: assert property (
        @(posedge clk) disable iff (!reset_n)
            ($past(reset_n) && !$past(debugack)) |-> (dbrk_break == ~$past(dbrk_break))
    );

    // dbrk_break holds when debugack is high in the previous cycle.
    check_dbrk_break_hold_on_ack_high: assert property (
        @(posedge clk) disable iff (!reset_n)
            ($past(reset_n) && $past(debugack)) |-> (dbrk_break == $past(dbrk_break))
    );

    // Trace/control-related outputs are always zero when not in reset.
    check_dbrk_static_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
            (dbrk_goto0 == 1'b0) &&
            (dbrk_goto1 == 1'b0) &&
            (dbrk_traceme == 1'b0) &&
            (dbrk_traceoff == 1'b0) &&
            (dbrk_traceon == 1'b0) &&
            (dbrk_trigout == 1'b0)
    );
endmodule