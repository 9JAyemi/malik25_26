module DOWNCOUNTER_POSEDGE_assertions #(parameter SIZE=16) (
    input logic Clock,
    input logic Reset,
    input logic [SIZE-1:0] Initial,
    input logic Enable,
    input logic [SIZE-1:0] Q
);

    // Reset loads Q from Initial.
    check_reset_load: assert property (
        @(posedge Clock) Reset |=> (Q == $past(Initial))
    );

    // When enabled outside reset, Q decrements by one.
    check_decrement_when_enabled: assert property (
        @(posedge Clock) disable iff (Reset) Enable |=> (Q == ($past(Q) - 1'b1))
    );

    // When disabled outside reset, Q holds its value.
    check_hold_when_disabled: assert property (
        @(posedge Clock) disable iff (Reset) !Enable |=> (Q == $past(Q))
    );

    // Decrementing zero wraps around to all ones.
    check_wrap_on_underflow: assert property (
        @(posedge Clock) disable iff (Reset) Enable && (Q == '0) |=> (Q == {SIZE{1'b1}})
    );

endmodule