module Comparator_sva (
    input logic clock,
    input logic [63:0] data,
    input logic [63:0] key,
    input logic match
);
    // Match equals the previous cycle's data==key result.
    check_match_reflects_prev_equality: assert property (
        @(posedge clock) $past(1'b1) |-> (match == $past(data == key))
    );

    // If data equals key this cycle, match will be 1 next cycle.
    check_next_match_set_on_equal: assert property (
        @(posedge clock) (data == key) |=> (match == 1'b1)
    );

    // If data differs from key this cycle, match will be 0 next cycle.
    check_next_match_clear_on_notequal: assert property (
        @(posedge clock) (data != key) |=> (match == 1'b0)
    );

    // When data and key are stable across cycles, match stays the same.
    check_stable_inputs_keep_match_stable: assert property (
        @(posedge clock) $past(1'b1) && (data == $past(data)) && (key == $past(key)) |-> (match == $past(match))
    );
endmodule