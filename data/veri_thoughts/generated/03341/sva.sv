module and2_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Q
);

    // Q matches the implemented NOR function of A and B.
    check_q_matches_nor: assert property (
        @(posedge clk) Q == (~A & ~B)
    );

    // Both inputs low drive Q high.
    check_both_low_drive_q_high: assert property (
        @(posedge clk) (!A && !B) |-> Q
    );

    // A high drives Q low.
    check_a_high_drives_q_low: assert property (
        @(posedge clk) A |-> !Q
    );

    // B high drives Q low.
    check_b_high_drives_q_low: assert property (
        @(posedge clk) B |-> !Q
    );

    // Both inputs high drive Q low.
    check_both_high_drive_q_low: assert property (
        @(posedge clk) (A && B) |-> !Q
    );

endmodule