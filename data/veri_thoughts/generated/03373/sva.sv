module sky130_fd_sc_lp__nor4b_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N
);

    // Purely combinational cell sampled on an external clock; no reset in RTL.

    // Y matches the NOR of A, B, C, and inverted D_N.
    check_nor4b_function: assert property (
        @(posedge clk) (Y == ~(A | B | C | (~D_N)))
    );

    // A high forces the NOR output low.
    check_a_high_forces_y_low: assert property (
        @(posedge clk) A |-> (Y == 1'b0)
    );

    // B high forces the NOR output low.
    check_b_high_forces_y_low: assert property (
        @(posedge clk) B |-> (Y == 1'b0)
    );

    // C high forces the NOR output low.
    check_c_high_forces_y_low: assert property (
        @(posedge clk) C |-> (Y == 1'b0)
    );

    // D_N low forces the inverted D input high, so Y must be low.
    check_dn_low_forces_y_low: assert property (
        @(posedge clk) (!D_N) |-> (Y == 1'b0)
    );

    // Y is high for the unique input combination A=B=C=0 and D_N=1.
    check_all_low_and_dn_high_sets_y: assert property (
        @(posedge clk) (!A && !B && !C && D_N) |-> (Y == 1'b1)
    );

    // Y high implies the unique enabling input combination.
    check_y_high_requires_unique_input_state: assert property (
        @(posedge clk) Y |-> (!A && !B && !C && D_N)
    );

endmodule