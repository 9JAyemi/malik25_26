module nor4b_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y must equal the 4-input NOR of A, B, C, and D_N.
    check_y_matches_nor_function: assert property (
        @(posedge clk) Y == ~(A | B | C | D_N)
    );

    // All four inputs low must drive Y high.
    check_all_inputs_low_drive_y_high: assert property (
        @(posedge clk) (!A && !B && !C && !D_N) |-> Y
    );

    // A high must force Y low.
    check_a_high_forces_y_low: assert property (
        @(posedge clk) A |-> !Y
    );

    // B high must force Y low.
    check_b_high_forces_y_low: assert property (
        @(posedge clk) B |-> !Y
    );

    // C high must force Y low.
    check_c_high_forces_y_low: assert property (
        @(posedge clk) C |-> !Y
    );

    // D_N high must force Y low.
    check_d_n_high_forces_y_low: assert property (
        @(posedge clk) D_N |-> !Y
    );

    // Y high implies all four inputs are low.
    check_y_high_implies_all_inputs_low: assert property (
        @(posedge clk) Y |-> (!A && !B && !C && !D_N)
    );

    // Y low implies at least one input is high.
    check_y_low_implies_some_input_high: assert property (
        @(posedge clk) !Y |-> (A || B || C || D_N)
    );

endmodule