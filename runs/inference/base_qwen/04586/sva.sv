module l1_data_cache_64entry_4way_line64b_bus_8b_disable_cache_sva (
    input wire iCLOCK,
    input wire inRESET,
    input wire iRESET_SYNC,
    input wire iREMOVE,
    input wire iRD_REQ,
    input wire iRD_BUSY,
    input wire [31:0] iRD_ADDR,
    input wire iUP_REQ,
    input wire iUP_BUSY,
    input wire [1:0] iUP_ORDER,
    input wire [3:0] iUP_MASK,
    input wire [31:0] iUP_ADDR,
    input wire [31:0] iUP_DATA,
    input wire iWR_REQ,
    input wire iWR_BUSY,
    input wire [31:0] iWR_ADDR,
    input wire [511:0] iWR_DATA,
    input wire [255:0] iWR_MMU_FLAGS
);
    // Sequential logic for request validation
    property p_req_valid;
        @(posedge iCLOCK) disable iff (!inRESET) b_req_valid |-> iRD_REQ;
    endproperty
    assert property (p_req_valid) else $error("Request validation failed");

    // Sequential logic for request busy handling
    property p_req_busy;
        @(posedge iCLOCK) disable iff (!inRESET) iRD_BUSY |-> oRD_BUSY;
    endproperty
    assert property (p_req_busy) else $error("Request busy handling failed");

    // Sequential logic for read valid handling
    property p_rd_valid;
        @(posedge iCLOCK) disable iff (!inRESET) b_req_valid |-> oRD_VALID;
    endproperty
    assert property (p_rd_valid) else $error("Read valid handling failed");

    // Sequential logic for read hit handling
    property p_rd_hit;
        @(posedge iCLOCK) disable iff (!inRESET) b_req_valid |-> oRD_HIT;
    endproperty
    assert property (p_rd_hit) else $error("Read hit handling failed");

    // Sequential logic for read data handling
    property p_rd_data;
        @(posedge iCLOCK) disable iff (!inRESET) b_req_valid |-> oRD_DATA == 32'h0;
    endproperty
    assert property (p_rd_data) else $error("Read data handling failed");

    // Sequential logic for update busy handling
    property p_up_busy;
        @(posedge iCLOCK) disable iff (!inRESET) iUP_REQ |-> oUP_BUSY;
    endproperty
    assert property (p_up_busy) else $error("Update busy handling failed");

    // Sequential logic for write busy handling
    property p_wr_busy;
        @(posedge iCLOCK) disable iff (!inRESET) iWR_REQ |-> oWR_BUSY;
    endproperty
    assert property (p_wr_busy) else $error("Write busy handling failed");

    // Sequential logic for request removal handling
    property p_req_removal;
        @(posedge iCLOCK) disable iff (!inRESET) iREMOVE |-> b_req_valid == 1'b0;
    endproperty
    assert property (p_req_removal) else $error("Request removal handling failed");

    // Sequential logic for reset handling
    property p_reset;
        @(posedge iCLOCK) disable iff (!inRESET) inRESET |-> (oRD_BUSY == 1'b0) && (oRD_VALID == 1'b0) && (oRD_HIT == 1'b0) && (oRD_DATA == 32'h0) && (oUP_BUSY == 1'b0) && (oWR_BUSY == 1'b0);
    endproperty
    assert property (p_reset) else $error("Reset handling failed");

    // Sequential logic for reset synchronization handling
    property p_reset_sync;
        @(posedge iCLOCK) disable iff (!inRESET) iRESET_SYNC |-> (oRD_BUSY == 1'b0) && (oRD_VALID == 1'b0) && (oRD_HIT == 1'b0) && (oRD_DATA == 32'h0) && (oUP_BUSY == 1'b0) && (oWR_BUSY == 1'b0);
    endproperty
    assert property (p_reset_sync) else $error("Reset synchronization handling failed");
endmodule