module BitLpf_sva #(
    parameter int FILT_BITS = 8
) (
    input  logic clk,
    input  logic rst,      // active-high synchronous reset
    input  logic en,
    input  logic dataIn,
    input  logic dataOut,
    input  logic signed [FILT_BITS-1:0] filter  // internal reg from DUT
);

    // dataOut is always the MSB of filter
    check_dataout_is_msb: assert property (
        @(posedge clk) disable iff (rst) dataOut == filter[FILT_BITS-1]
    );

    // On the first cycle after reset was asserted, filter is zero
    check_filter_zero_after_reset: assert property (
        @(posedge clk) disable iff (rst) $past(rst) |-> (filter == {FILT_BITS{1'b0}})
    );

    // On the first cycle after reset was asserted, dataOut is zero
    check_out_zero_after_reset: assert property (
        @(posedge clk) disable iff (rst) $past(rst) |-> (dataOut == 1'b0)
    );

    // When en was LOW and not in reset, filter holds its value
    check_filter_hold_when_en_low: assert property (
        @(posedge clk) disable iff (rst) $past(!rst && !en) |-> (filter == $past(filter))
    );

    // When en was HIGH but dataIn==dataOut, filter holds (delta=0)
    check_filter_hold_when_no_delta: assert property (
        @(posedge clk) disable iff (rst) $past(!rst && en && ($past(dataIn) == $past(dataOut))) |-> (filter == $past(filter))
    );

    // When en was HIGH and not in reset, filter updates by (dataIn - dataOut)
    check_filter_update_when_en_high: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst && en) |-> (
                filter == ($signed($past(filter))
                           + $signed({{(FILT_BITS-1){1'b0}}, $past(dataIn)})
                           - $signed({{(FILT_BITS-1){1'b0}}, $past(dataOut)}))
            )
    );

    // When en was LOW and not in reset, dataOut holds (filter holds)
    check_out_hold_when_en_low: assert property (
        @(posedge clk) disable iff (rst) $past(!rst && !en) |-> (dataOut == $past(dataOut))
    );

    // When en was HIGH but dataIn==dataOut, dataOut holds
    check_out_hold_when_no_delta: assert property (
        @(posedge clk) disable iff (rst) $past(!rst && en && ($past(dataIn) == $past(dataOut))) |-> (dataOut == $past(dataOut))
    );

    // A change on dataOut requires prior en HIGH and dataIn!=dataOut
    check_out_change_requires_update: assert property (
        @(posedge clk) disable iff (rst) (dataOut != $past(dataOut)) |-> ($past(!rst && en) && ($past(dataIn) != $past(dataOut)))
    );

    // A change on filter requires prior en HIGH (outside reset)
    check_filter_change_requires_en: assert property (
        @(posedge clk) disable iff (rst) (filter != $past(filter)) |-> $past(en)
    );

endmodule