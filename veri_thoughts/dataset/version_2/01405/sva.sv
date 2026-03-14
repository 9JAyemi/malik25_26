module my_module_sva (
    input logic clk,
    input logic rst,
    input logic [31:0] in_data,
    input logic [31:0] out_data
);
    // Next-state equation: out_data equals (prev rst ? 0 : prev in_data).
    check_next_state_equation: assert property (
        @(posedge clk) $past(1'b1) |-> (out_data == ($past(rst) ? 32'd0 : $past(in_data)))
    );

    // When rst is HIGH, out_data becomes 0 on the following cycle.
    check_reset_clears_on_next: assert property (
        @(posedge clk) rst |=> (out_data == 32'd0)
    );

    // While rst remains HIGH across cycles, out_data stays 0.
    check_hold_zero_during_reset: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (out_data == 32'd0)
    );

    // On rst deassertion, next out_data equals current in_data.
    check_deassert_passthrough: assert property (
        @(posedge clk) $fell(rst) |=> (out_data == $past(in_data))
    );

    // In back-to-back non-reset cycles, out_data equals previous in_data.
    check_passthrough_no_reset: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) |-> (out_data == $past(in_data))
    );

    // If in_data changes in a non-reset cycle, out_data changes on the next cycle.
    check_input_change_propagates: assert property (
        @(posedge clk) disable iff (rst) ($past(!rst) && $changed(in_data)) |=> $changed(out_data)
    );

    // If in_data is stable in a non-reset cycle, out_data does not change next cycle.
    check_output_stable_if_input_stable: assert property (
        @(posedge clk) disable iff (rst) ($past(!rst) && !$changed(in_data)) |=> !$changed(out_data)
    );
endmodule