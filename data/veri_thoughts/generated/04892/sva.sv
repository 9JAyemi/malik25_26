module sky130_fd_sc_hd__xnor2_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Y
);

    // Pure combinational XNOR sampled on an external clock.

    // Y must always equal A XNOR B.
    check_xnor_function: assert property (
        @(posedge clk) Y == (A ~^ B)
    );

    // Equal low inputs drive Y high.
    check_both_low_drive_high: assert property (
        @(posedge clk) (!A && !B) |-> Y
    );

    // A low and B high drive Y low.
    check_a_low_b_high_drive_low: assert property (
        @(posedge clk) (!A && B) |-> !Y
    );

    // A high and B low drive Y low.
    check_a_high_b_low_drive_low: assert property (
        @(posedge clk) (A && !B) |-> !Y
    );

    // Equal high inputs drive Y high.
    check_both_high_drive_high: assert property (
        @(posedge clk) (A && B) |-> Y
    );

endmodule