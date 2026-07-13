module ZigbeeReceiver_sva #(
    parameter int n = 8
) (
    input logic carrier,
    input logic modulated,
    input logic en,
    input logic clk,
    input logic [n-1:0] out
);

    // out follows the registered function of the prior cycle inputs.
    check_registered_function: assert property (
        @(posedge clk) 1'b1 |=> (out == ($past(en && carrier) ? {n{$past(modulated)}} : {n{1'b0}}))
    );

    // When enabled with carrier, out captures the replicated modulated bit.
    check_active_capture: assert property (
        @(posedge clk) (en && carrier) |=> (out == {n{$past(modulated)}})
    );

    // When not enabled or no carrier, out goes to zero on the next cycle.
    check_inactive_zero: assert property (
        @(posedge clk) (!en || !carrier) |=> (out == {n{1'b0}})
    );

    // An active high modulated bit produces all ones.
    check_active_one_fill: assert property (
        @(posedge clk) (en && carrier && modulated) |=> (out == {n{1'b1}})
    );

    // An active low modulated bit produces all zeros.
    check_active_zero_fill: assert property (
        @(posedge clk) (en && carrier && !modulated) |=> (out == {n{1'b0}})
    );

    // Disabling the receiver forces out low on the next cycle.
    check_disable_forces_zero: assert property (
        @(posedge clk) (!en) |=> (out == {n{1'b0}})
    );

    // No carrier forces out low on the next cycle.
    check_no_carrier_forces_zero: assert property (
        @(posedge clk) (!carrier) |=> (out == {n{1'b0}})
    );

endmodule