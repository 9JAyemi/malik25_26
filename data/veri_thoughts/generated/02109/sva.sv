module up_down_counter_sva (
    input logic CLK,
    input logic UP_DOWN,
    input logic RESET,
    input logic [3:0] Q
);
    // On RESET high, next-cycle Q is cleared to 0.
    reset_clears_next: assert property (
        @(posedge CLK) RESET |=> (Q == 4'b0000)
    );

    // While RESET is held high across cycles, Q remains 0.
    reset_holds_zero: assert property (
        @(posedge CLK) ($past(RESET) && RESET) |-> (Q == 4'b0000)
    );

    // With UP_DOWN=1, Q increments by 1 next cycle (mod 16).
    count_up_step: assert property (
        @(posedge CLK) disable iff (RESET) (UP_DOWN) |=> (Q == ($past(Q) + 4'd1))
    );

    // With UP_DOWN=0, Q decrements by 1 next cycle (mod 16).
    count_down_step: assert property (
        @(posedge CLK) disable iff (RESET) (!UP_DOWN) |=> (Q == ($past(Q) - 4'd1))
    );

    // Up-count wraps from F to 0.
    up_wrap: assert property (
        @(posedge CLK) disable iff (RESET) ($past(Q) == 4'hF && UP_DOWN) |=> (Q == 4'h0)
    );

    // Down-count wraps from 0 to F.
    down_wrap: assert property (
        @(posedge CLK) disable iff (RESET) ($past(Q) == 4'h0 && !UP_DOWN) |=> (Q == 4'hF)
    );

    // Two consecutive UP cycles produce a net +2 over two cycles.
    double_up_step: assert property (
        @(posedge CLK) disable iff (RESET)
            (UP_DOWN && $past(UP_DOWN) && !$past(RESET)) |=> |=> (Q == ($past($past(Q)) + 4'd2))
    );

    // Two consecutive DOWN cycles produce a net -2 over two cycles.
    double_down_step: assert property (
        @(posedge CLK) disable iff (RESET)
            (!UP_DOWN && !$past(UP_DOWN) && !$past(RESET)) |=> |=> (Q == ($past($past(Q)) - 4'd2))
    );

    // UP then DOWN over two cycles returns Q to its original value.
    up_then_down_no_net: assert property (
        @(posedge CLK) disable iff (RESET) (UP_DOWN ##1 !UP_DOWN) |=> (Q == $past(Q,2))
    );

    // DOWN then UP over two cycles returns Q to its original value.
    down_then_up_no_net: assert property (
        @(posedge CLK) disable iff (RESET) (!UP_DOWN ##1 UP_DOWN) |=> (Q == $past(Q,2))
    );

    // Next-cycle Q always matches prev Q plus (+1 for UP, -1 for DOWN) when not in RESET.
    next_matches_dir: assert property (
        @(posedge CLK) disable iff (RESET) 1'b1 |=> (Q == ($past(Q) + (UP_DOWN ? 4'd1 : 4'hF)))
    );
endmodule