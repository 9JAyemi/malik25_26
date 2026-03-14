module top_module_sva (
    input  logic        clk,
    input  logic        up_down,
    input  logic        load,
    input  logic        select,
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic [2:0]  count,
    input  logic [7:0]  P
);

    ///// Output muxing rules /////
    // When select is HIGH, count is forced to zero.
    check_count_masked_by_select: assert property (
        @(posedge clk) select |-> (count == 3'd0)
    );

    // When select is HIGH, P is forced to zero.
    check_p_masked_by_select: assert property (
        @(posedge clk) select |-> (P == 8'd0)
    );

    ///// Multiplier behavior /////
    // When select is LOW, P equals A*B.
    check_multiplier_function_unselected: assert property (
        @(posedge clk) !select |-> (P == (A * B))
    );

    ///// Counter behavior (visible at top when not masked) /////
    // A load pulse clears the counter on the next cycle.
    check_counter_load_clears_next: assert property (
        @(posedge clk) load |=> (count == 3'd0)
    );

    // When output is visible (past and current select LOW), next count follows RTL update function.
    check_counter_update_visible: assert property (
        @(posedge clk)
        ($past(select) == 1'b0 && !select) |-> (
            count ==
            ( $past(load) ? 3'd0
                          : ( $past(up_down)
                              ? (($past(count) + 3'd1)[2:0])
                              : (($past(count) - 3'd1)[2:0]) ) )
        )
    );

    // When counting up and output visible, count increments modulo 8.
    check_counter_inc_visible: assert property (
        @(posedge clk)
        ($past(select) == 1'b0 && !select && $past(load) == 1'b0 && $past(up_down) == 1'b1)
        |-> (count == (($past(count) + 3'd1)[2:0]))
    );

    // When counting down and output visible, count decrements modulo 8.
    check_counter_dec_visible: assert property (
        @(posedge clk)
        ($past(select) == 1'b0 && !select && $past(load) == 1'b0 && $past(up_down) == 1'b0)
        |-> (count == (($past(count) - 3'd1)[2:0]))
    );

    // When counting (no load) and output visible, count changes every cycle.
    check_counter_changes_when_counting: assert property (
        @(posedge clk)
        ($past(select) == 1'b0 && !select && $past(load) == 1'b0)
        |-> (count != $past(count))
    );

endmodule