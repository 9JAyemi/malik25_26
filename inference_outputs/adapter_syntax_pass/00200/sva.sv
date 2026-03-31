module sky130_fd_sc_hd__nor4_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Y must equal the 4-input NOR of A, B, C, and D.
    check_nor_function: assert property (
        @(posedge clk) Y == ~(A | B | C | D)
    );

    // All inputs low must drive Y high.
    check_all_inputs_low_drive_high: assert property (
        @(posedge clk) (!A && !B && !C && !D) |-> Y
    );

    // A high must force Y low.
    check_a_high_forces_low: assert property (
        @(posedge clk) A |-> !Y
    );

    // B high must force Y low.
    check_b_high_forces_low: assert property (
        @(posedge clk) B |-> !Y
    );

    // C high must force Y low.
    check_c_high_forces_low: assert property (
        @(posedge clk) C |-> !Y
    );

    // D high must force Y low.
    check_d_high_forces_low: assert property (
        @(posedge clk) D |-> !Y
    );

    // Y high implies all inputs are low.
    check_y_high_implies_all_inputs_low: assert property (
        @(posedge clk) Y |-> (!A && !B && !C && !D)
    );

    // Y low implies at least one input is high.
    check_y_low_implies_some_input_high: assert property (
        @(posedge clk) !Y |-> (A || B || C || D)
    );

endmodule