module ZigbeeReceiver_sva #(
    parameter int n = 8
)(
    input logic carrier,
    input logic modulated,
    input logic en,
    input logic clk,
    input logic [n-1:0] out
);

    // Enabled carrier loads the output with the current modulated value.
    check_load_on_enabled_carrier: assert property (
        @(posedge clk) (en && carrier) |=> (out == {n{modulated}})
    );

    // Disabled carrier clears the output.
    check_clear_when_disabled_carrier: assert property (
        @(posedge clk) (!en || !carrier) |=> (out == {n{1'b0}})
    );

    // A high output must come from a previous enabled carrier cycle.
    check_high_output_requires_prev_enabled_carrier: assert property (
        @(posedge clk) 1'b1 |=> ((out == {n{1'b0}}) || $past(en && carrier))
    );

    // A low output can come from a previous disabled carrier cycle or a zero load.
    check_low_output_requires_prev_disabled_carrier_or_zero_load: assert property (
        @(posedge clk) 1'b1 |=> ((out == {n{1'b1}}) || $past(!en || !carrier) || ($past(en && carrier) && ($past(modulated) == 1'b0)))
    );

endmodule