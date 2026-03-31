module l1_data_cache_64entry_4way_line64b_bus_8b_disable_cache_sva (
    input logic iCLOCK,
    input logic inRESET,
    input logic iRESET_SYNC,
    input logic iREMOVE,
    input logic iRD_REQ,
    input logic oRD_BUSY,
    input logic [31:0] iRD_ADDR,
    input logic oRD_VALID,
    input logic oRD_HIT,
    input logic iRD_BUSY,
    input logic [31:0] oRD_DATA,
    input logic [11:0] oRD_MMU_FLAGS,
    input logic iUP_REQ,
    input logic oUP_BUSY,
    input logic [1:0] iUP_ORDER,
    input logic [3:0] iUP_MASK,
    input logic [31:0] iUP_ADDR,
    input logic [31:0] iUP_DATA,
    input logic iWR_REQ,
    input logic oWR_BUSY,
    input logic [31:0] iWR_ADDR,
    input logic [511:0] iWR_DATA,
    input logic [255:0] iWR_MMU_FLAGS
);

// oRD_BUSY is permanently asserted low.
    check_rd_busy_low: assert property (
        @(posedge iCLOCK) disable iff (!inRESET) (oRD_BUSY == 1'b0)
    );

// oRD_VALID is a registered copy of iRD_REQ.
    check_rd_valid_registered: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
            $past(!inRESET) |-> (oRD_VALID == $past(iRD_REQ))
    );

// oRD_VALID is low when iRESET_SYNC is high.
    check_rd_valid_sync_reset: assert property (
        @(posedge iCLOCK) disable iff (!inRESET) (iRESET_SYNC == 1'b1) |-> (oRD_VALID == 1'b0)
    );

// oRD_VALID is low when iREMOVE is high.
    check_rd_valid_remove: assert property (
        @(posedge iCLOCK) disable iff (!inRESET) (iREMOVE == 1'b1) |-> (oRD_VALID == 1'b0)
    );

// oRD_VALID is high when iRD_REQ is high and iRESET_SYNC/iREMOVE are low.
    check_rd_valid_request: assert property (
        @(posedge iCLOCK) disable iff (!inRESET) (iRD_REQ && !iRESET_SYNC && !iREMOVE) |-> (oRD_VALID == 1'b1)
    );

// oRD_HIT is permanently asserted low.
    check_rd_hit_low: assert property (
        @(posedge iCLOCK) disable iff (!inRESET) (oRD_HIT == 1'b0)
    );

// oRD_DATA is permanently asserted zero.
    check_rd_data_zero: assert property (
        @(posedge iCLOCK) disable iff (!inRESET) (oRD_DATA == 32'h0)
    );

// oRD_MMU_FLAGS is permanently asserted zero.
    check_rd_mmu_zero: assert property (
        @(posedge iCLOCK) disable iff (!inRESET) (oRD_MMU_FLAGS == 12'h0)
    );

// oUP_BUSY is permanently asserted low.
    check_up_busy_low: assert property (
        @(posedge iCLOCK) disable iff (!inRESET) (oUP_BUSY == 1'b0)
    );

// oWR_BUSY is permanently asserted low.
    check_wr_busy_low: assert property (
        @(posedge iCLOCK) disable iff (!inRESET) (oWR_BUSY == 1'b0)
    );

endmodule
