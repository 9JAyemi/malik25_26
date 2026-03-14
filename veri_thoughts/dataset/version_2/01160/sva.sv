module d_ff_en_parameterized_sva #(
    parameter WIDTH = 1,
    parameter INIT  = 0
) (
    input logic                 CLK,
    input logic                 E,
    input logic [WIDTH-1:0]     D,
    input logic [WIDTH-1:0]     Q
);
    // Clock: CLK. No reset port. Sequential D-FF with enable E; Q captures D when E is high.

    // On enable, Q captures D on the next clock.
    check_capture_on_enable: assert property (
        @(posedge CLK) E |=> (Q == $past(D))
    );

    // When disabled, Q holds its previous value on the next clock.
    check_hold_when_disabled: assert property (
        @(posedge CLK) !E |=> (Q == $past(Q))
    );

    // Next-state function: Q_next = (E ? D : Q) based on previous cycle.
    check_next_state_definition: assert property (
        @(posedge CLK) 1'b1 |=> (Q == ($past(E) ? $past(D) : $past(Q)))
    );

    // A change in Q across a cycle requires that enable was high in the previous cycle.
    check_change_requires_enable: assert property (
        @(posedge CLK) 1'b1 |=> ( ($past(E)) || (Q == $past(Q)) )
    );

    // If enable was high in the previous cycle, Q equals the previous D value.
    check_prev_enable_implies_q_prev_d: assert property (
        @(posedge CLK) $past(E) |-> (Q == $past(D))
    );

endmodule