module _4bit_down_counter_with_synch_load_enable_clear_sva (
    input logic       Clock,
    input logic       Clear,
    input logic       Enable,
    input logic       Load,
    input logic [3:0] Q
);

    // Clear synchronously sets Q to all ones.
    check_clear_sets_q_to_ones: assert property (
        @(posedge Clock) disable iff (1'b0)
        Clear |=> (Q == 4'hF)
    );

    // Enable decrements Q when Load is low.
    check_enable_decrements_q: assert property (
        @(posedge Clock) disable iff (1'b0)
        (!Clear && Enable && !Load) |=> (Q == ($past(Q) - 4'd1))
    );

    // Enable takes priority over Load.
    check_enable_has_priority_over_load: assert property (
        @(posedge Clock) disable iff (1'b0)
        (!Clear && Enable && Load) |=> (Q == ($past(Q) - 4'd1))
    );

    // Load sets Q to all ones when selected.
    check_load_sets_q_to_ones: assert property (
        @(posedge Clock) disable iff (1'b0)
        (!Clear && !Enable && Load) |=> (Q == 4'hF)
    );

    // Q holds its value when no control is asserted.
    check_hold_without_controls: assert property (
        @(posedge Clock) disable iff (1'b0)
        (!Clear && !Enable && !Load) |=> (Q == $past(Q))
    );

    // Decrement wraps from zero back to all ones.
    check_decrement_wraps_from_zero: assert property (
        @(posedge Clock) disable iff (1'b0)
        (!Clear && Enable && (Q == 4'h0)) |=> (Q == 4'hF)
    );

endmodule