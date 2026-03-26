module DFlipFlop_sva (
    input logic clk,
    input logic reset,
    input logic d,
    input logic q
);

    // clk is the clock; reset is an active-low asynchronous reset; q captures d on rising clk.
    
    // q is held low whenever reset is asserted.
    check_q_low_during_reset: assert property (
        @(posedge clk)
        !reset |-> (q == 1'b0)
    );

    // q is still low on the first clock edge after reset is released.
    check_q_low_on_reset_release: assert property (
        @(posedge clk)
        (!reset ##1 reset) |-> (q == 1'b0)
    );

    // q becomes 1 on the next clock when d is 1 in normal operation.
    check_q_captures_one: assert property (
        @(posedge clk) disable iff (!reset)
        d |=> (q == 1'b1)
    );

    // q becomes 0 on the next clock when d is 0 in normal operation.
    check_q_captures_zero: assert property (
        @(posedge clk) disable iff (!reset)
        !d |=> (q == 1'b0)
    );

endmodule