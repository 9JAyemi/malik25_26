module l1_data_cache_64entry_4way_line64b_bus_8b_disable_cache_sva (
    input logic         iCLOCK,
    input logic         inRESET,
    input logic         iRESET_SYNC,
    input logic         iREMOVE,
    input logic         iRD_REQ,
    input logic         oRD_BUSY,
    input logic [31:0]  iRD_ADDR,
    input logic         oRD_VALID,
    input logic         oRD_HIT,
    input logic         iRD_BUSY,
    input logic [31:0]  oRD_DATA,
    input logic [11:0]  oRD_MMU_FLAGS,
    input logic         iUP_REQ,
    input logic         oUP_BUSY,
    input logic [1:0]   iUP_ORDER,
    input logic [3:0]   iUP_MASK,
    input logic [31:0]  iUP_ADDR,
    input logic [31:0]  iUP_DATA,
    input logic         iWR_REQ,
    input logic         oWR_BUSY,
    input logic [31:0]  iWR_ADDR,
    input logic [511:0] iWR_DATA,
    input logic [255:0] iWR_MMU_FLAGS
);

    // Read busy is permanently deasserted.
    check_rd_busy_constant_low: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (oRD_BUSY == 1'b0)
    );

    // Read MMU flags are permanently zero.
    check_rd_mmu_flags_constant_zero: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (oRD_MMU_FLAGS == 12'h000)
    );

    // Read hit is permanently deasserted.
    check_rd_hit_constant_low: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (oRD_HIT == 1'b0)
    );

    // Read data is permanently zero.
    check_rd_data_constant_zero: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (oRD_DATA == 32'h00000000)
    );

    // Update busy is permanently deasserted.
    check_up_busy_constant_low: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (oUP_BUSY == 1'b0)
    );

    // Write busy is permanently deasserted.
    check_wr_busy_constant_low: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (oWR_BUSY == 1'b0)
    );

    // Sync reset or remove clears the registered read valid on the next cycle.
    check_rd_valid_clears_on_sync_reset_or_remove: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (iRESET_SYNC || iREMOVE) |=> (oRD_VALID == 1'b0)
    );

    // Without clear conditions, a high read request sets read valid on the next cycle.
    check_rd_valid_sets_from_rd_req: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (!iRESET_SYNC && !iREMOVE && iRD_REQ) |=> (oRD_VALID == 1'b1)
    );

    // Without clear conditions, a low read request clears read valid on the next cycle.
    check_rd_valid_clears_from_rd_req_low: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (!iRESET_SYNC && !iREMOVE && !iRD_REQ) |=> (oRD_VALID == 1'b0)
    );

    // After reset is released, read valid starts low.
    check_rd_valid_low_on_reset_release: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        $rose(inRESET) |-> (oRD_VALID == 1'b0)
    );

endmodule