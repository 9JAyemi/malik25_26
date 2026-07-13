module dff_sva (
    input logic DATAIN,
    input logic CLK,
    input logic ACLR,
    input logic ENA,
    input logic SCLR,
    input logic SLOAD,
    input logic SDATA,
    input logic Q
);
    // Asynchronous clear holds Q low while asserted.
    check_async_clear_forces_zero: assert property (
        @(posedge CLK) !ACLR |-> (Q == 1'b0)
    );

    // With ENA high and SCLR high, Q synchronously clears to 0.
    check_sync_clear_when_enabled: assert property (
        @(posedge CLK) disable iff (!ACLR) (ENA && SCLR) |-> (Q == 1'b0)
    );

    // With ENA high, SCLR low, and SLOAD high, Q loads SDATA.
    check_sync_load_when_enabled: assert property (
        @(posedge CLK) disable iff (!ACLR) (ENA && !SCLR && SLOAD) |-> (Q == SDATA)
    );

    // With ENA high and both SCLR and SLOAD low, Q captures DATAIN.
    check_data_capture_when_enabled: assert property (
        @(posedge CLK) disable iff (!ACLR) (ENA && !SCLR && !SLOAD) |-> (Q == DATAIN)
    );

    // When enabled and not synchronously cleared, Q equals SLOAD ? SDATA : DATAIN.
    check_combined_mux_behavior: assert property (
        @(posedge CLK) disable iff (!ACLR) (ENA && !SCLR) |-> (Q == (SLOAD ? SDATA : DATAIN))
    );

    // Synchronous clear has priority over SLOAD when both are high.
    check_sclr_overrides_sload: assert property (
        @(posedge CLK) disable iff (!ACLR) (ENA && SCLR && SLOAD) |-> (Q == 1'b0)
    );

    // When enabled, Q equals (SCLR ? 0 : (SLOAD ? SDATA : DATAIN)).
    check_full_case_when_enabled: assert property (
        @(posedge CLK) disable iff (!ACLR) ENA |-> (Q == (SCLR ? 1'b0 : (SLOAD ? SDATA : DATAIN)))
    );
endmodule