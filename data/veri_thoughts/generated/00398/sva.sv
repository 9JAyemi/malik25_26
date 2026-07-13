module MISTRAL_FF_sva (
    input logic DATAIN,
    input logic CLK,
    input logic ACLR,
    input logic ENA,
    input logic SCLR,
    input logic SLOAD,
    input logic SDATA,
    input logic Q
);

    // Q starts low from the RTL initial assignment.
    check_init_q_low: assert property (
        @(posedge CLK) $initstate |-> (Q == 1'b0)
    );

    // A low ACLR leaves Q low until the next clock sample.
    check_aclr_forces_zero: assert property (
        @(posedge CLK) !ACLR |=> (Q == 1'b0)
    );

    // Enabled synchronous clear drives Q low.
    check_sclr_clears_q: assert property (
        @(posedge CLK) disable iff (!ACLR)
        (ENA && SCLR) |=> (Q == 1'b0)
    );

    // Enabled synchronous load captures a 0 from SDATA.
    check_sload_captures_zero: assert property (
        @(posedge CLK) disable iff (!ACLR)
        (ENA && !SCLR && SLOAD && !SDATA) |=> (Q == 1'b0)
    );

    // Enabled data capture takes a 0 from DATAIN.
    check_datain_captures_zero: assert property (
        @(posedge CLK) disable iff (!ACLR)
        (ENA && !SCLR && !SLOAD && !DATAIN) |=> (Q == 1'b0)
    );

    // With ENA low, a low Q is held across the clock edge.
    check_ena_low_holds_zero: assert property (
        @(posedge CLK) disable iff (!ACLR)
        (!ENA && (Q == 1'b0)) |=> (Q == 1'b0)
    );

    // SCLR overrides SLOAD when both are asserted.
    check_sclr_priority_over_sload: assert property (
        @(posedge CLK) disable iff (!ACLR)
        (ENA && SCLR && SLOAD) |=> (Q == 1'b0)
    );

    // SLOAD selects SDATA over DATAIN when clear is inactive.
    check_sload_priority_over_datain: assert property (
        @(posedge CLK) disable iff (!ACLR)
        (ENA && !SCLR && SLOAD && !SDATA && DATAIN) |=> (Q == 1'b0)
    );

    // When SLOAD is low, SDATA does not affect DATAIN capture.
    check_datain_path_ignores_sdata: assert property (
        @(posedge CLK) disable iff (!ACLR)
        (ENA && !SCLR && !SLOAD && !DATAIN && SDATA) |=> (Q == 1'b0)
    );

endmodule