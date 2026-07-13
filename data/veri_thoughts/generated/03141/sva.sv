module sky130_fd_sc_ms__nor4_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Y must always be the 4-input NOR of A, B, C, and D.
    check_nor4_function: assert property (
        @(posedge clk) Y == ~(A | B | C | D)
    );

    // If all inputs are low, Y must be high.
    check_all_inputs_low_drive_high: assert property (
        @(posedge clk) (!A && !B && !C && !D) |-> Y
    );

    // If A is high, Y must be low.
    check_a_high_drives_low: assert property (
        @(posedge clk) A |-> !Y
    );

    // If B is high, Y must be low.
    check_b_high_drives_low: assert property (
        @(posedge clk) B |-> !Y
    );

    // If C is high, Y must be low.
    check_c_high_drives_low: assert property (
        @(posedge clk) C |-> !Y
    );

    // If D is high, Y must be low.
    check_d_high_drives_low: assert property (
        @(posedge clk) D |-> !Y
    );

    // If Y is high, all inputs must be low.
    check_y_high_implies_all_inputs_low: assert property (
        @(posedge clk) Y |-> (!A && !B && !C && !D)
    );

endmodule