module dps_main_counter_sva (
    input logic        iCLOCK,
    input logic        inRESET,
    input logic        iCONF_WRITE,
    input logic        iCONF_ENA,
    input logic        iCOUNT_WRITE,
    input logic [1:0]  inCOUNT_DQM,
    input logic [63:0] iCOUNT_COUNTER,
    input logic        oWORKING,
    input logic [63:0] oCOUNTER
);

    // Reset clears working and counter.
    check_reset_clears_state: assert property (
        @(posedge iCLOCK) !inRESET |-> (oWORKING == 1'b0 && oCOUNTER == 64'h0)
    );

    // A configuration write updates working from iCONF_ENA.
    check_conf_write_updates_working: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        iCONF_WRITE |=> (oWORKING == $past(iCONF_ENA))
    );

    // Without a configuration write, working holds its value.
    check_working_holds_without_conf_write: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        !iCONF_WRITE |=> (oWORKING == $past(oWORKING))
    );

    // When working is set, the counter increments by one.
    check_working_increments_counter: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        oWORKING |=> (oCOUNTER == ($past(oCOUNTER) + 64'd1))
    );

    // When stopped and not writing, the counter holds.
    check_stopped_no_write_holds_counter: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (!oWORKING && !iCOUNT_WRITE) |=> (oCOUNTER == $past(oCOUNTER))
    );

    // When stopped and low word is unmasked, bits [31:0] load from iCOUNT_COUNTER.
    check_stopped_write_loads_low_half: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (!oWORKING && iCOUNT_WRITE && !inCOUNT_DQM[0]) |=> (oCOUNTER[31:0] == $past(iCOUNT_COUNTER[31:0]))
    );

    // When stopped and low word is masked, bits [31:0] hold.
    check_stopped_write_masks_low_half: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (!oWORKING && iCOUNT_WRITE && inCOUNT_DQM[0]) |=> (oCOUNTER[31:0] == $past(oCOUNTER[31:0]))
    );

    // When stopped and high word is unmasked, bits [63:32] load from iCOUNT_COUNTER.
    check_stopped_write_loads_high_half: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (!oWORKING && iCOUNT_WRITE && !inCOUNT_DQM[1]) |=> (oCOUNTER[63:32] == $past(iCOUNT_COUNTER[63:32]))
    );

    // When stopped and high word is masked, bits [63:32] hold.
    check_stopped_write_masks_high_half: assert property (
        @(posedge iCLOCK) disable iff (!inRESET)
        (!oWORKING && iCOUNT_WRITE && inCOUNT_DQM[1]) |=> (oCOUNTER[63:32] == $past(oCOUNTER[63:32]))
    );

endmodule