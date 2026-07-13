module ddr3_s4_uniphy_example_if0_p0_qsys_sequencer_cpu_inst_nios2_oci_fifowp_inc_sva (
    input logic        free2,
    input logic        free3,
    input logic [1:0]  tm_count,
    input logic [3:0]  fifowp_inc
);

    // free3 has highest priority when tm_count is 3.
    check_free3_priority_at_count3: assert property (
        @($global_clock) (free3 && (tm_count == 2'd3)) |-> (fifowp_inc == 4'd3)
    );

    // At tm_count 2, free2 selects an increment of 2.
    check_count2_with_free2: assert property (
        @($global_clock) ((tm_count == 2'd2) && free2) |-> (fifowp_inc == 4'd2)
    );

    // At tm_count 2 without free2, the increment falls back to 1.
    check_count2_without_free2: assert property (
        @($global_clock) ((tm_count == 2'd2) && !free2) |-> (fifowp_inc == 4'd1)
    );

    // At tm_count 3 without free3, free2 selects an increment of 2.
    check_count3_with_free2_without_free3: assert property (
        @($global_clock) ((tm_count == 2'd3) && !free3 && free2) |-> (fifowp_inc == 4'd2)
    );

    // At tm_count 3 without free3 or free2, the increment falls back to 1.
    check_count3_without_free3_or_free2: assert property (
        @($global_clock) ((tm_count == 2'd3) && !free3 && !free2) |-> (fifowp_inc == 4'd1)
    );

    // At tm_count 1, the increment is 1 regardless of free inputs.
    check_count1_output: assert property (
        @($global_clock) (tm_count == 2'd1) |-> (fifowp_inc == 4'd1)
    );

    // At tm_count 0, the increment is 0 regardless of free inputs.
    check_count0_output: assert property (
        @($global_clock) (tm_count == 2'd0) |-> (fifowp_inc == 4'd0)
    );

    // The output only encodes values 0 through 3.
    check_output_upper_bits_zero: assert property (
        @($global_clock) (fifowp_inc[3:2] == 2'b00)
    );

    // The output matches the complete combinational decision tree.
    check_full_decision_tree: assert property (
        @($global_clock)
        (fifowp_inc ==
            ((tm_count == 2'd3) ? (free3 ? 4'd3 : (free2 ? 4'd2 : 4'd1)) :
             (tm_count == 2'd2) ? (free2 ? 4'd2 : 4'd1) :
             (tm_count == 2'd1) ? 4'd1 :
                                  4'd0))
    );

endmodule