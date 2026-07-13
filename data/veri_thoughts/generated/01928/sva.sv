module my_nor_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C
);
    // No explicit clock/reset in RTL; pure combinational. Use any input edge as the clocking event.

    // Y equals (~C) & (A | B).
    check_y_function_equivalence: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        Y == ((~C) & (A | B))
    );

    // If C is HIGH, Y is LOW.
    check_c_high_forces_y_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        C |-> (Y == 1'b0)
    );

    // If C is LOW, Y equals A OR B.
    check_c_low_defines_y: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        (!C) |-> (Y == (A | B))
    );

    // If A and B are both LOW, Y is LOW (independent of C).
    check_a_b_both_low_y_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        (!A && !B) |-> (Y == 1'b0)
    );

    // With C LOW and A HIGH, Y is HIGH.
    check_c_low_a_high_y_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        (!C && A) |-> (Y == 1'b1)
    );

    // With C LOW and B HIGH, Y is HIGH.
    check_c_low_b_high_y_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        (!C && B) |-> (Y == 1'b1)
    );

    // If Y is HIGH then C must be LOW.
    check_y_high_implies_c_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        Y |-> (!C)
    );

    // If Y is HIGH then A or B must be HIGH.
    check_y_high_implies_a_or_b_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C)
        Y |-> (A || B)
    );

    // On rising edge of C, Y must be driven LOW.
    check_y_low_on_c_rise: assert property (
        @(posedge C) (Y == 1'b0)
    );

    // On falling edge of C, Y equals A OR B.
    check_y_matches_or_on_c_fall: assert property (
        @(negedge C) (Y == (A | B))
    );

endmodule