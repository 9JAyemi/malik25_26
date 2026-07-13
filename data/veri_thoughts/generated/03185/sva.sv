module up_down_counter_sva (
    input logic       CLK,
    input logic       UP_DOWN,
    input logic       RESET,
    input logic [3:0] OUT
);

    // Reset clears the counter to zero.
    check_reset_clears_out: assert property (
        @(posedge CLK) RESET |=> (OUT == 4'b0000)
    );

    // UP_DOWN high increments the counter on the next clock.
    check_increment_when_up: assert property (
        @(posedge CLK) disable iff (RESET)
        UP_DOWN |=> (OUT == ($past(OUT) + 4'd1))
    );

    // UP_DOWN low decrements the counter on the next clock.
    check_decrement_when_down: assert property (
        @(posedge CLK) disable iff (RESET)
        !UP_DOWN |=> (OUT == ($past(OUT) - 4'd1))
    );

    // Counting up wraps from 15 back to 0.
    check_increment_wrap: assert property (
        @(posedge CLK) disable iff (RESET)
        (UP_DOWN && (OUT == 4'hF)) |=> (OUT == 4'h0)
    );

    // Counting down wraps from 0 back to 15.
    check_decrement_wrap: assert property (
        @(posedge CLK) disable iff (RESET)
        (!UP_DOWN && (OUT == 4'h0)) |=> (OUT == 4'hF)
    );

endmodule