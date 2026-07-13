module nios_dut_nios2_gen2_0_cpu_nios2_oci_fifo_wrptr_inc_sva (
    input logic       ge2_free,
    input logic       ge3_free,
    input logic [1:0] input_tm_cnt,
    input logic [3:0] fifo_wrptr_inc
);

    // Output must match the RTL's combinational branch ordering.
    check_output_matches_rtl: assert property (
        @($global_clock)
        fifo_wrptr_inc == (
            (ge3_free && (input_tm_cnt == 2'b11)) ? 4'b0011 :
            (ge2_free && (input_tm_cnt >= 2'd2)) ? 4'b0010 :
            (input_tm_cnt >= 2'd1)               ? 4'b0001 :
                                                   4'b0000
        )
    );

    // The ge3_free path has highest priority when the count is 3.
    check_ge3_priority: assert property (
        @($global_clock)
        (ge3_free && (input_tm_cnt == 2'b11)) |-> (fifo_wrptr_inc == 4'b0011)
    );

    // The ge2_free path selects an increment of 2 when the ge3_free path is not taken.
    check_ge2_branch: assert property (
        @($global_clock)
        (!(ge3_free && (input_tm_cnt == 2'b11)) &&
         ge2_free &&
         (input_tm_cnt >= 2'd2)) |-> (fifo_wrptr_inc == 4'b0010)
    );

    // The fallback nonzero path selects an increment of 1 when earlier paths are not taken.
    check_single_increment_branch: assert property (
        @($global_clock)
        (!(ge3_free && (input_tm_cnt == 2'b11)) &&
         !(ge2_free && (input_tm_cnt >= 2'd2)) &&
         (input_tm_cnt >= 2'd1)) |-> (fifo_wrptr_inc == 4'b0001)
    );

    // A zero input count produces a zero increment.
    check_zero_count_branch: assert property (
        @($global_clock)
        (input_tm_cnt == 2'd0) |-> (fifo_wrptr_inc == 4'b0000)
    );

    // The upper two output bits are always zero.
    check_upper_bits_zero: assert property (
        @($global_clock)
        fifo_wrptr_inc[3:2] == 2'b00
    );

endmodule