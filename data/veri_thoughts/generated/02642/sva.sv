module top_module_sva (
    input logic        clk,
    input logic [7:0]  address,
    input logic [3:0]  byteenable,
    input logic        wren,
    input logic [31:0] data_in,
    input logic [31:0] data_out
);
    ///// Analysis summary /////
    // Clock: clk; no reset in RTL.
    // Logic: mixed (combinational mux feeding a registered output).
    // Behavior: on each rising clk, if previous wren then data_out loads previous data_in; else holds.

    ///// Functional properties /////
    // Next data_out equals previous-cycle mux result: wren ? data_in : data_out.
    check_output_update_rule: assert property (
        @(posedge clk) $past(1'b1) |-> data_out == ($past(wren) ? $past(data_in) : $past(data_out))
    );

    // When previous wren is LOW, data_out holds its value.
    check_hold_when_wren_low: assert property (
        @(posedge clk) $past(1'b1) && !$past(wren) |-> data_out == $past(data_out)
    );

    // When previous wren is HIGH, data_out loads previous data_in.
    check_load_when_wren_high: assert property (
        @(posedge clk) $past(1'b1) && $past(wren) |-> data_out == $past(data_in)
    );

    // Any change in data_out must be caused by previous wren HIGH.
    check_change_requires_prev_write: assert property (
        @(posedge clk) $past(1'b1) && (data_out != $past(data_out)) |-> $past(wren)
    );

    // If wren was LOW for two consecutive past cycles, data_out equals its value from two cycles ago.
    check_two_cycle_hold_no_write: assert property (
        @(posedge clk) $past(1'b1,2) && !$past(wren) && !$past(wren,2) |-> data_out == $past(data_out,2)
    );

    // Address changes with previous wren LOW do not change data_out.
    check_addr_change_no_effect_without_write: assert property (
        @(posedge clk) $past(1'b1) && !$past(wren) && $changed(address) |-> data_out == $past(data_out)
    );

    // Byteenable changes with previous wren LOW do not change data_out.
    check_byteenable_change_no_effect_without_write: assert property (
        @(posedge clk) $past(1'b1) && !$past(wren) && $changed(byteenable) |-> data_out == $past(data_out)
    );
endmodule