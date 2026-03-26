module niosii_nios2_gen2_0_cpu_nios2_oci_dbrk_sva (
    input logic [31:0] E_st_data,
    input logic [31:0] av_ld_data_aligned_filtered,
    input logic clk,
    input logic [22:0] d_address,
    input logic d_read,
    input logic d_waitrequest,
    input logic d_write,
    input logic debugack,
    input logic reset_n,
    input logic [22:0] cpu_d_address,
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

    // cpu_d_address mirrors d_address.
    check_cpu_d_address_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) (cpu_d_address == d_address)
    );

    // cpu_d_read mirrors d_read.
    check_cpu_d_read_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) (cpu_d_read == d_read)
    );

    // cpu_d_readdata mirrors av_ld_data_aligned_filtered.
    check_cpu_d_readdata_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) (cpu_d_readdata == av_ld_data_aligned_filtered)
    );

    // cpu_d_writedata mirrors E_st_data.
    check_cpu_d_writedata_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) (cpu_d_writedata == E_st_data)
    );

    // cpu_d_write mirrors d_write.
    check_cpu_d_write_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) (cpu_d_write == d_write)
    );

    // cpu_d_wait mirrors d_waitrequest.
    check_cpu_d_wait_passthrough: assert property (
        @(posedge clk) disable iff (!reset_n) (cpu_d_wait == d_waitrequest)
    );

    // dbrk_break is low while reset is asserted.
    check_dbrk_break_reset_low: assert property (
        @(posedge clk) (!reset_n) |-> (dbrk_break == 1'b0)
    );

    // dbrk_break never asserts after reset.
    check_dbrk_break_stays_low: assert property (
        @(posedge clk) disable iff (!reset_n) (dbrk_break == 1'b0)
    );

    // dbrk_goto0 is tied low.
    check_dbrk_goto0_low: assert property (
        @(posedge clk) disable iff (!reset_n) (dbrk_goto0 == 1'b0)
    );

    // dbrk_goto1 is tied low.
    check_dbrk_goto1_low: assert property (
        @(posedge clk) disable iff (!reset_n) (dbrk_goto1 == 1'b0)
    );

    // dbrk_traceme is tied low.
    check_dbrk_traceme_low: assert property (
        @(posedge clk) disable iff (!reset_n) (dbrk_traceme == 1'b0)
    );

    // dbrk_traceoff is tied low.
    check_dbrk_traceoff_low: assert property (
        @(posedge clk) disable iff (!reset_n) (dbrk_traceoff == 1'b0)
    );

    // dbrk_traceon is tied low.
    check_dbrk_traceon_low: assert property (
        @(posedge clk) disable iff (!reset_n) (dbrk_traceon == 1'b0)
    );

    // dbrk_trigout is tied low.
    check_dbrk_trigout_low: assert property (
        @(posedge clk) disable iff (!reset_n) (dbrk_trigout == 1'b0)
    );

endmodule