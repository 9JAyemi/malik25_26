module ZigbeeReceiver_sva #(
    parameter n = 8
)(
    input logic carrier,
    input logic modulated,
    input logic en,
    input logic clk,
    input logic [n-1:0] out
);

    // When enabled and carrier is high, out loads the replicated modulated value.
    check_load_on_enable: assert property (
        @(posedge clk) (en && carrier) |=> (out == {n{modulated}})
    );

    // When enabled and carrier is low, out loads all zeros.
    check_zero_on_enable_without_carrier: assert property (
        @(posedge clk) (en && !carrier) |=> (out == {n{1'b0}})
    );

    // When not enabled, out clears to zero.
    check_clear_when_disabled: assert property (
        @(posedge clk) (!en) |=> (out == {n{1'b0}})
    );

    // out always matches the previous cycle's enabled-load or clear behavior.
    check_out_update_function: assert property (
        @(posedge clk) 1'b1 |=> (out == ($past(en) ? {n{$past(modulated)}} : {n{1'b0}}))
    );

endmodule