module mux_2to1_priority_sva (
    // External sampling clock (RTL has no clock/reset)
    input logic clk,
    // DUT ports
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       P,
    input logic [3:0] Y
);
    // Y must equal the selected input each cycle.
    check_mux_function: assert property (
        @(posedge clk) Y == (P ? A : B)
    );

    // When P is 1, Y must equal A.
    check_select_A_when_P_high: assert property (
        @(posedge clk) P |-> (Y == A)
    );

    // When P is 0, Y must equal B.
    check_select_B_when_P_low: assert property (
        @(posedge clk) !P |-> (Y == B)
    );

    // If A, B, and P are all stable, Y must be stable.
    check_stable_when_all_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(P)) |-> $stable(Y)
    );

    // With P held high and A stable, changes on B must not affect Y.
    check_unselected_B_ignored_when_P_high: assert property (
        @(posedge clk) (P && $stable(P) && $stable(A) && !$stable(B)) |-> $stable(Y)
    );

    // With P held low and B stable, changes on A must not affect Y.
    check_unselected_A_ignored_when_P_low: assert property (
        @(posedge clk) (!P && $stable(P) && $stable(B) && !$stable(A)) |-> $stable(Y)
    );

    // With P held high, a change on A must cause a change on Y.
    check_y_follows_A_when_P_high: assert property (
        @(posedge clk) (P && $stable(P) && !$stable(A)) |-> !$stable(Y)
    );

    // With P held low, a change on B must cause a change on Y.
    check_y_follows_B_when_P_low: assert property (
        @(posedge clk) (!P && $stable(P) && !$stable(B)) |-> !$stable(Y)
    );

    // On rising P, Y must now equal A and previously have equaled B.
    check_behavior_on_P_rise: assert property (
        @(posedge clk) $rose(P) |-> (Y == A) && ($past(Y) == $past(B))
    );

    // On falling P, Y must now equal B and previously have equaled A.
    check_behavior_on_P_fall: assert property (
        @(posedge clk) $fell(P) |-> (Y == B) && ($past(Y) == $past(A))
    );
endmodule