module Contador_Ascendente_Descendente_sva
#(
    parameter N = 4
) (
    input logic clk,
    input logic reset,
    input logic enUP,
    input logic enDOWN,
    input logic [N-1:0] q
);

    // Reset forces the counter output to zero.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |-> (q == '0)
    );

    // With both enables low, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        (!enUP && !enDOWN) |=> (q == $past(q))
    );

    // enUP makes the counter increment on the next clock.
    check_increment_on_enUP: assert property (
        @(posedge clk) disable iff (reset)
        enUP |=> (q == ($past(q) + 1'b1))
    );

    // enDOWN alone makes the counter decrement on the next clock.
    check_decrement_on_enDOWN: assert property (
        @(posedge clk) disable iff (reset)
        (!enUP && enDOWN) |=> (q == ($past(q) - 1'b1))
    );

    // If both enables are high, enUP has priority over enDOWN.
    check_enUP_priority: assert property (
        @(posedge clk) disable iff (reset)
        (enUP && enDOWN) |=> (q == ($past(q) + 1'b1))
    );

endmodule