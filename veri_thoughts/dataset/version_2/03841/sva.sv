module up_down_counter_assertions (
    input logic clk,
    input logic [2:0] D,
    input logic L,
    input logic U,
    input logic [2:0] out
);

    // When L was high, out must load the previous D value.
    check_load_behavior: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(L) |-> (out == $past(D))
    );

    // When L was low and U was high, out must increment.
    check_count_up_behavior: assert property (
        @(posedge clk) disable iff ($initstate)
        (!$past(L) && $past(U)) |-> (out == ($past(out) + 3'd1))
    );

    // When both L and U were low, out must decrement.
    check_count_down_behavior: assert property (
        @(posedge clk) disable iff ($initstate)
        (!$past(L) && !$past(U)) |-> (out == ($past(out) - 3'd1))
    );

    // out must always match the RTL next-state function.
    check_next_state_function: assert property (
        @(posedge clk) disable iff ($initstate)
        out == ($past(L) ? $past(D) : ($past(U) ? ($past(out) + 3'd1) : ($past(out) - 3'd1)))
    );

endmodule