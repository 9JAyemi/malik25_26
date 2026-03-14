module Problem2_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic F,
    input logic X,
    input logic Y
);
    // Y must always be the logical complement of X.
    check_y_is_complement_of_x: assert property (
        @($global_clock) Y == ~X
    );

    // X must be 1 when at least four inputs among A..F are 1.
    check_x_high_when_ge4: assert property (
        @($global_clock) ($countones({A,B,C,D,E,F}) >= 4) |-> (X == 1'b1)
    );

    // X must be 0 when fewer than four inputs among A..F are 1.
    check_x_low_when_lt4: assert property (
        @($global_clock) ($countones({A,B,C,D,E,F}) < 4) |-> (X == 1'b0)
    );

    // If no input rises, X cannot rise (monotonic non-decreasing w.r.t. input rises).
    check_no_x_rise_without_input_rise: assert property (
        @($global_clock) !($rose(A) || $rose(B) || $rose(C) || $rose(D) || $rose(E) || $rose(F)) |-> !$rose(X)
    );

    // If no input falls, X cannot fall (monotonic non-increasing w.r.t. input falls).
    check_no_x_fall_without_input_fall: assert property (
        @($global_clock) !($fell(A) || $fell(B) || $fell(C) || $fell(D) || $fell(E) || $fell(F)) |-> !$fell(X)
    );

    // If all inputs are stable, both outputs must be stable (purely combinational function).
    check_stable_inputs_hold_outputs: assert property (
        @($global_clock) $stable({A,B,C,D,E,F}) |-> ($stable(X) && $stable(Y))
    );

    // When X rises, the popcount must cross from <4 to >=4.
    check_x_rise_crosses_threshold: assert property (
        @($global_clock) $rose(X) |-> (($countones({A,B,C,D,E,F}) >= 4) && ($countones($past({A,B,C,D,E,F})) < 4))
    );

    // When X falls, the popcount must cross from >=4 to <4.
    check_x_fall_crosses_threshold: assert property (
        @($global_clock) $fell(X) |-> (($countones({A,B,C,D,E,F}) < 4) && ($countones($past({A,B,C,D,E,F})) >= 4))
    );
endmodule