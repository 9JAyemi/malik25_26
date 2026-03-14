module soc_design_SystemID_sva (
    input logic clock,
    input logic reset_n,
    input logic [31:0] address,
    input logic [31:0] readdata
);
    // During reset, readdata is 0.
    check_reset_forces_zero: assert property (
        @(posedge clock) (!reset_n) |-> (readdata == 32'h00000000)
    );

    // On falling edge of reset_n, readdata is 0 at this sample.
    check_reset_fall_clears_output: assert property (
        @(posedge clock) $fell(reset_n) |-> (readdata == 32'h00000000)
    );

    // On rising edge of reset_n, readdata remains 0 in this cycle.
    check_reset_rise_zero_this_cycle: assert property (
        @(posedge clock) $rose(reset_n) |-> (readdata == 32'h00000000)
    );

    // Out of reset, readdata equals function of previous-cycle address.
    check_prev_addr_mapping: assert property (
        @(posedge clock) disable iff (!reset_n)
            $past(reset_n) |-> (readdata == (($past(address) == 32'h00000000) ? 32'h000000FF : 32'h590D8D31))
    );

    // When operational, readdata is one of the two allowed constants.
    check_operational_value_domain: assert property (
        @(posedge clock) disable iff (!reset_n)
            $past(reset_n) |-> (readdata inside {32'h000000FF, 32'h590D8D31})
    );

    // When operational, readdata is never zero.
    check_operational_nonzero: assert property (
        @(posedge clock) disable iff (!reset_n)
            $past(reset_n) |-> (readdata != 32'h00000000)
    );

    // If address==0 and remain out of reset, next-cycle readdata is 0xFF.
    check_forward_pipeline_zero: assert property (
        @(posedge clock) disable iff (!reset_n)
            (address == 32'h00000000) |-> ##1 (reset_n && (readdata == 32'h000000FF))
    );

    // If address!=0 and remain out of reset, next-cycle readdata is 0x590D8D31.
    check_forward_pipeline_nonzero: assert property (
        @(posedge clock) disable iff (!reset_n)
            (address != 32'h00000000) |-> ##1 (reset_n && (readdata == 32'h590D8D31))
    );

    // With two-cycle stable address and out of reset, readdata stays stable.
    check_stable_address_two_cycles_keeps_output_stable: assert property (
        @(posedge clock) disable iff (!reset_n)
            ($past(reset_n) && $past(reset_n,2) && ($past(address) == $past(address,2))) |-> (readdata == $past(readdata))
    );

    // With two cycles out of reset, both current and previous outputs match their respective address mappings.
    check_two_cycle_correlation: assert property (
        @(posedge clock) disable iff (!reset_n)
            ($past(reset_n) && $past(reset_n,2)) |-> 
            (($past(readdata) == (($past(address,2) == 32'h00000000) ? 32'h000000FF : 32'h590D8D31)) &&
             (readdata       == (($past(address)    == 32'h00000000) ? 32'h000000FF : 32'h590D8D31)))
    );
endmodule