module nios_dut_nios2_gen2_0_cpu_nios2_oci_im_sva (
    input logic        clk,
    input logic        jrst_n,
    input logic [15:0] trc_ctrl,
    input logic [35:0] tw,
    input logic        tracemem_on,
    input logic [35:0] tracemem_trcdata,
    input logic        tracemem_tw,
    input logic [6:0]  trc_im_addr,
    input logic        trc_wrap,
    input logic        xbrk_wrap_traceoff
);

    // Reset clears the address and wrap state.
    check_reset_clears_state: assert property (
        @(posedge clk) !jrst_n |-> (trc_im_addr == 7'd0) && (trc_wrap == 1'b0)
    );

    // tracemem_on is the inverse of trc_ctrl[8].
    check_tracemem_on_decode: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (tracemem_on == (~trc_ctrl[8]))
    );

    // tracemem_trcdata is always zero.
    check_tracemem_trcdata_zero: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (tracemem_trcdata == 36'd0)
    );

    // tracemem_tw reflects whether the trace word header is nonzero.
    check_tracemem_tw_decode: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (tracemem_tw == (tw[35:32] != 4'b0000))
    );

    // xbrk_wrap_traceoff is trc_ctrl[10] AND trc_wrap.
    check_xbrk_wrap_traceoff_decode: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (xbrk_wrap_traceoff == (trc_ctrl[10] & trc_wrap))
    );

    // A wrap condition clears the address and deasserts wrap on the next cycle.
    check_wrap_clears_next_cycle: assert property (
        @(posedge clk) disable iff (!jrst_n)
        trc_wrap |=> (!trc_wrap && (trc_im_addr == 7'd0))
    );

    // Without wrap, a valid trace word increments the address.
    check_addr_increments_on_valid: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (!trc_wrap && (tw[35:32] != 4'b0000)) |=> (trc_im_addr == ($past(trc_im_addr) + 7'd1))
    );

    // Without wrap and without a valid trace word, the address holds.
    check_addr_holds_on_no_valid: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (!trc_wrap && (tw[35:32] == 4'b0000)) |=> (trc_im_addr == $past(trc_im_addr))
    );

    // Reaching the terminal address asserts wrap on the next cycle.
    check_wrap_sets_at_terminal_addr: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (!trc_wrap && (trc_im_addr == 7'h7F)) |=> trc_wrap
    );

    // Before the terminal address, wrap remains deasserted.
    check_wrap_stays_low_before_terminal_addr: assert property (
        @(posedge clk) disable iff (!jrst_n)
        (!trc_wrap && (trc_im_addr != 7'h7F)) |=> !trc_wrap
    );

endmodule