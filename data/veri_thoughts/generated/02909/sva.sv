module top_module_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [31:0] data_in,
    input logic [31:0] data_out
);
    // Reset drives data_out to zero on the active clock edge.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |-> (data_out == 32'h0000_0000)
    );

    // With enable asserted (and not in reset), next cycle data_out equals current data_in.
    check_load_on_enable_next: assert property (
        @(posedge clk) disable iff (reset) (enable && $past(1'b1)) |=> (data_out == $past(data_in))
    );

    // When disabled (and not in reset), data_out holds its previous value into the next cycle.
    check_hold_when_disabled_next: assert property (
        @(posedge clk) disable iff (reset) (!enable && $past(1'b1)) |=> (data_out == $past(data_out))
    );

    // When disabled (and not in reset), data_out is unchanged at this clock edge.
    check_no_immediate_change_when_disabled: assert property (
        @(posedge clk) disable iff (reset) (!enable && $past(1'b1)) |-> (data_out == $past(data_out))
    );

    // Without reset, any change on data_out implies enable is asserted this cycle.
    check_output_change_requires_enable: assert property (
        @(posedge clk) disable iff (reset) ($changed(data_out) && $past(1'b1)) |-> enable
    );

    // After a reset cycle, if still disabled now, data_out remains zero.
    check_hold_zero_after_reset_until_enable: assert property (
        @(posedge clk) disable iff (reset) ($past(1'b1) && $past(reset) && !enable) |-> (data_out == 32'h0000_0000)
    );
endmodule