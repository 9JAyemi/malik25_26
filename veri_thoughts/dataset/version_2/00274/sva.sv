module NV_NVDLA_RT_cacc2glb_sva (
    input logic        nvdla_core_clk,
    input logic        nvdla_core_rstn,
    input logic [1:0]  cacc2glb_done_intr_src_pd,
    input logic [1:0]  cacc2glb_done_intr_dst_pd
);

    // Reset forces the destination bus low.
    check_reset_clears_dst: assert property (
        @(posedge nvdla_core_clk)
        !nvdla_core_rstn |-> (cacc2glb_done_intr_dst_pd == 2'b00)
    );

    // The first clock after reset release still holds the cleared value.
    check_first_cycle_after_reset_release_zero: assert property (
        @(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
        !$past(nvdla_core_rstn) |-> (cacc2glb_done_intr_dst_pd == 2'b00)
    );

    // The second clock after reset release reflects the prior cycle source.
    check_second_cycle_after_reset_release_matches_src_d1: assert property (
        @(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
        $past(nvdla_core_rstn) && !$past(nvdla_core_rstn, 2)
        |-> (cacc2glb_done_intr_dst_pd == $past(cacc2glb_done_intr_src_pd))
    );

    // After two active clocks out of reset, destination is source delayed by two cycles.
    check_steady_state_two_cycle_delay: assert property (
        @(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
        $past(nvdla_core_rstn) && $past(nvdla_core_rstn, 2)
        |-> (cacc2glb_done_intr_dst_pd == $past(cacc2glb_done_intr_src_pd, 2))
    );

    // Bit 0 follows the same two-cycle delay in steady state.
    check_steady_state_bit0_two_cycle_delay: assert property (
        @(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
        $past(nvdla_core_rstn) && $past(nvdla_core_rstn, 2)
        |-> (cacc2glb_done_intr_dst_pd[0] == $past(cacc2glb_done_intr_src_pd[0], 2))
    );

    // Bit 1 follows the same two-cycle delay in steady state.
    check_steady_state_bit1_two_cycle_delay: assert property (
        @(posedge nvdla_core_clk) disable iff (!nvdla_core_rstn)
        $past(nvdla_core_rstn) && $past(nvdla_core_rstn, 2)
        |-> (cacc2glb_done_intr_dst_pd[1] == $past(cacc2glb_done_intr_src_pd[1], 2))
    );

endmodule