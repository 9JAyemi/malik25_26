module counter_4bit_sva (
    input logic clk,
    input logic reset,
    input logic up_down,
    input logic load,
    input logic [3:0] D,
    input logic [3:0] Q
);
    // On reset high, next Q is cleared to 0.
    reset_clears_Q: assert property (
        @(posedge clk) reset |=> (Q == 4'b0000)
    );

    // When load is high (and not in reset), next Q equals D.
    load_writes_D: assert property (
        @(posedge clk) disable iff (reset) load |=> (Q == $past(D))
    );

    // When counting up without wrap (Q != 15) and no load, next Q = Q + 1.
    increment_when_up_no_wrap: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down && (Q != 4'hF)) |=> (Q == ($past(Q) + 4'd1))
    );

    // When counting down without wrap (Q != 0) and no load, next Q = Q - 1.
    decrement_when_down_no_wrap: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down && (Q != 4'h0)) |=> (Q == ($past(Q) - 4'd1))
    );

    // Counting up from 15 wraps to 0 when no load.
    wrap_on_increment_from_max: assert property (
        @(posedge clk) disable iff (reset) (!load && up_down && (Q == 4'hF)) |=> (Q == 4'h0)
    );

    // Counting down from 0 wraps to 15 when no load.
    wrap_on_decrement_from_min: assert property (
        @(posedge clk) disable iff (reset) (!load && !up_down && (Q == 4'h0)) |=> (Q == 4'hF)
    );

    // Exact next-state function when not in reset.
    next_state_function: assert property (
        @(posedge clk) disable iff (reset)
            1'b1 |=> Q == ($past(load)
                           ? $past(D)
                           : ($past(up_down)
                              ? (($past(Q) == 4'hF) ? 4'h0 : ($past(Q) + 4'd1))
                              : (($past(Q) == 4'h0) ? 4'hF : ($past(Q) - 4'd1))))
    );

    // When counting (no load), Q always changes next cycle.
    count_changes_without_load: assert property (
        @(posedge clk) disable iff (reset) (!load) |=> (Q != $past(Q))
    );
endmodule