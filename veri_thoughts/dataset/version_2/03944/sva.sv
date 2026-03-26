module arr_sva (
    input logic        clk,
    input logic        duv_rst_ip,
    input logic [31:0] out
);

    // posedge clk is the only clock; duv_rst_ip is an active-high synchronous reset.
    // The design is a sequential counter with a combinational output mirror.

    // A reset cycle forces the next sampled output to zero.
    check_reset_clears_out: assert property (
        @(posedge clk) duv_rst_ip |=> (out == 32'd0)
    );

    // Two consecutive non-reset cycles increment the output by one.
    check_out_increments_without_reset: assert property (
        @(posedge clk) disable iff (duv_rst_ip)
        (!duv_rst_ip ##1 !duv_rst_ip) |-> (out == ($past(out) + 32'd1))
    );

    // If reset stays asserted for two cycles, the later sampled output is zero.
    check_out_zero_during_held_reset: assert property (
        @(posedge clk) duv_rst_ip ##1 duv_rst_ip |-> (out == 32'd0)
    );

    // When reset is released after a reset cycle, the first non-reset sample is zero.
    check_first_cycle_after_reset_release_is_zero: assert property (
        @(posedge clk) duv_rst_ip ##1 !duv_rst_ip |-> (out == 32'd0)
    );

    // One cycle after reset release, the counter advances to one.
    check_second_cycle_after_reset_release_is_one: assert property (
        @(posedge clk) duv_rst_ip ##1 !duv_rst_ip |=> (out == 32'd1)
    );

    // The 32-bit counter wraps from all ones to zero on the next non-reset cycle.
    check_out_wraps_after_max: assert property (
        @(posedge clk) disable iff (duv_rst_ip)
        (out == 32'hFFFF_FFFF) |=> (out == 32'd0)
    );

endmodule