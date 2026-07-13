module execute_forwarding_register_sva (
    input logic        iCLOCK,
    input logic        inRESET,
    input logic        iRESET_SYNC,
    input logic        iWB_GR_VALID,
    input logic [31:0] iWB_GR_DATA,
    input logic [4:0]  iWB_GR_DEST,
    input logic        iWB_GR_DEST_SYSREG,
    input logic        iWB_SPR_VALID,
    input logic [31:0] iWB_SPR_DATA,
    input logic        iWB_AUTO_SPR_VALID,
    input logic [31:0] iWB_AUTO_SPR_DATA,
    input logic [31:0] iCUUR_SPR_DATA,
    input logic        iWB_FRCR_VALID,
    input logic [63:0] iWB_FRCR_DATA,
    input logic [63:0] iCUUR_FRCR_DATA,
    input logic        oFDR_GR_VALID,
    input logic [31:0] oFDR_GR_DATA,
    input logic [4:0]  oFDR_GR_DEST,
    input logic        oFDR_GR_DEST_SYSREG,
    input logic        oFDR_SPR_VALID,
    input logic [31:0] oFDR_SPR_DATA,
    input logic        oFDR_FRCR_VALID,
    input logic [63:0] oFDR_FRCR_DATA
);

    // Low async reset clears all forwarding outputs by the next clock sample.
    check_async_reset_clears_outputs: assert property (
        @(posedge iCLOCK)
        !inRESET |=> (
            (oFDR_GR_VALID == 1'b0) &&
            (oFDR_GR_DATA == 32'h0) &&
            (oFDR_GR_DEST == 5'h0) &&
            (oFDR_GR_DEST_SYSREG == 1'b0) &&
            (oFDR_SPR_VALID == 1'b0) &&
            (oFDR_SPR_DATA == 32'h0) &&
            (oFDR_FRCR_VALID == 1'b0) &&
            (oFDR_FRCR_DATA == 64'h0)
        )
    );

    // High sync reset clears all forwarding outputs on the next clock.
    check_sync_reset_clears_outputs: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        iRESET_SYNC |=> (
            (oFDR_GR_VALID == 1'b0) &&
            (oFDR_GR_DATA == 32'h0) &&
            (oFDR_GR_DEST == 5'h0) &&
            (oFDR_GR_DEST_SYSREG == 1'b0) &&
            (oFDR_SPR_VALID == 1'b0) &&
            (oFDR_SPR_DATA == 32'h0) &&
            (oFDR_FRCR_VALID == 1'b0) &&
            (oFDR_FRCR_DATA == 64'h0)
        )
    );

    // A valid GR write captures data and destination.
    check_gr_capture_on_valid: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (!iRESET_SYNC && iWB_GR_VALID) |=> (
            (oFDR_GR_VALID == 1'b1) &&
            (oFDR_GR_DATA == $past(iWB_GR_DATA)) &&
            (oFDR_GR_DEST == $past(iWB_GR_DEST)) &&
            (oFDR_GR_DEST_SYSREG == $past(iWB_GR_DEST_SYSREG))
        )
    );

    // Without a valid GR write, the GR forwarding state holds.
    check_gr_hold_without_write: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (!iRESET_SYNC && !iWB_GR_VALID) |=> (
            $stable(oFDR_GR_VALID) &&
            $stable(oFDR_GR_DATA) &&
            $stable(oFDR_GR_DEST) &&
            $stable(oFDR_GR_DEST_SYSREG)
        )
    );

    // WB SPR write has priority and sets SPR valid.
    check_spr_capture_from_wb: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (!iRESET_SYNC && iWB_SPR_VALID) |=> (
            (oFDR_SPR_VALID == 1'b1) &&
            (oFDR_SPR_DATA == $past(iWB_SPR_DATA))
        )
    );

    // Auto SPR write forwards auto data and leaves valid low.
    check_spr_capture_from_auto: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (!iRESET_SYNC && !iWB_SPR_VALID && iWB_AUTO_SPR_VALID) |=> (
            (oFDR_SPR_VALID == 1'b0) &&
            (oFDR_SPR_DATA == $past(iWB_AUTO_SPR_DATA))
        )
    );

    // Without SPR writes, current SPR data is forwarded with valid high.
    check_spr_forward_current_data: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (!iRESET_SYNC && !iWB_SPR_VALID && !iWB_AUTO_SPR_VALID) |=> (
            (oFDR_SPR_VALID == 1'b1) &&
            (oFDR_SPR_DATA == $past(iCUUR_SPR_DATA))
        )
    );

    // A valid FRCR write captures FRCR data.
    check_frcr_capture_from_wb: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (!iRESET_SYNC && iWB_FRCR_VALID) |=> (
            (oFDR_FRCR_VALID == 1'b1) &&
            (oFDR_FRCR_DATA == $past(iWB_FRCR_DATA))
        )
    );

    // Without an FRCR write, current FRCR data is forwarded with valid high.
    check_frcr_forward_current_data: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (!iRESET_SYNC && !iWB_FRCR_VALID) |=> (
            (oFDR_FRCR_VALID == 1'b1) &&
            (oFDR_FRCR_DATA == $past(iCUUR_FRCR_DATA))
        )
    );

endmodule