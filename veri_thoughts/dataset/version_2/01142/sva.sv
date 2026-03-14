module top_module_sva (
    input logic clk,
    input logic reset,          // Synchronous active-high reset
    input logic [7:0] d,
    input logic select,
    input logic [7:0] q,
    // Internal observation points from the RTL hierarchy
    input logic [7:0] reg_output,
    input logic [3:0] counter_output,
    input logic [7:0] active_output,
    input logic [7:0] adder_input
);
    ///// register_module checks /////
    // After a cycle with reset asserted, register outputs 0x34.
    check_register_reset_value: assert property (
        @(posedge clk) $past(reset) |-> (reg_output == 8'h34)
    );
    // When not in reset on consecutive cycles, register captures previous d.
    check_register_captures_d: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (reg_output == $past(d))
    );

    ///// counter_module checks /////
    // After a cycle with reset asserted, counter outputs 0.
    check_counter_reset_value: assert property (
        @(posedge clk) $past(reset) |-> (counter_output == 4'd0)
    );
    // When not in reset on consecutive cycles, counter increments by 1 (mod-16).
    check_counter_increments: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (counter_output == $past(counter_output) + 4'd1)
    );

    ///// adder_module checks /////
    // Adder output equals reg_output plus zero-extended counter_output.
    check_adder_sum: assert property (
        @(posedge clk) disable iff (reset) adder_input == (reg_output + {4'b0, counter_output})
    );

    ///// control_module mux checks /////
    // When select=1, active_output comes from adder_input.
    check_mux_select1: assert property (
        @(posedge clk) disable iff (reset) (select) |-> (active_output == adder_input)
    );
    // When select=0, active_output passes reg_output (LSBs of {zero, reg_output}).
    check_mux_select0: assert property (
        @(posedge clk) disable iff (reset) (!select) |-> (active_output == reg_output)
    );

    ///// top_module connectivity checks /////
    // Top-level q follows active_output.
    check_q_follows_active_output: assert property (
        @(posedge clk) disable iff (reset) (q == active_output)
    );
    // When select=1, q equals reg_output plus zero-extended counter_output.
    check_q_select1_sum: assert property (
        @(posedge clk) disable iff (reset) (select) |-> (q == (reg_output + {4'b0, counter_output}))
    );
    // When select=0, q equals reg_output.
    check_q_select0_passthrough: assert property (
        @(posedge clk) disable iff (reset) (!select) |-> (q == reg_output)
    );
    // When select=0 and previous cycle not reset, q equals previous d.
    check_q_select0_matches_past_d: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) && (!select) |-> (q == $past(d))
    );
endmodule