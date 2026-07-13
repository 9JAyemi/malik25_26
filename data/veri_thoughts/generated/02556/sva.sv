module Adder_sva (
    input logic [2:0] A,
    input logic [2:0] B,
    input logic CLK,
    input logic RST,
    input logic [2:0] Q
);
    // Q is 0 whenever RST is asserted at the clock edge.
    check_q_zero_when_rst_high: assert property (
        @(posedge CLK) RST |-> (Q == 3'b000)
    );

    // When not in reset, Q equals A+B computed at that edge.
    check_q_equals_sum_when_not_reset: assert property (
        @(posedge CLK) disable iff (RST) (Q == (A + B))
    );

    // On a rising edge of RST, Q is forced to 0 in that cycle.
    check_reset_rise_forces_zero: assert property (
        @(posedge CLK) $rose(RST) |-> (Q == 3'b000)
    );

    // On a falling edge of RST, Q loads A+B in that cycle.
    check_reset_fall_loads_sum: assert property (
        @(posedge CLK) disable iff (RST) $fell(RST) |-> (Q == (A + B))
    );

    // If reset is high in two consecutive cycles, Q is 0 in both.
    check_hold_zero_during_reset: assert property (
        @(posedge CLK) RST && $past(RST) |-> (Q == 3'b000) && ($past(Q) == 3'b000)
    );

    // With reset low in consecutive cycles and A,B stable, Q remains stable.
    check_q_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (RST) $past(!RST) && $stable(A) && $stable(B) |-> (Q == $past(Q))
    );
endmodule