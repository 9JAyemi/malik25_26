module sky130_fd_sc_hd__nor4_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Y must equal the NOR of all four inputs.
    check_nor_function: assert property (
        @(posedge clk) Y == ~(A | B | C | D)
    );

    // All inputs low must drive Y high.
    check_all_inputs_low_drives_y_high: assert property (
        @(posedge clk) (!A && !B && !C && !D) |-> Y
    );

    // Any high input must drive Y low.
    check_any_input_high_drives_y_low: assert property (
        @(posedge clk) (A || B || C || D) |-> !Y
    );

    // A high Y means all inputs are low.
    check_y_high_implies_all_inputs_low: assert property (
        @(posedge clk) Y |-> (!A && !B && !C && !D)
    );

    // A low Y means at least one input is high.
    check_y_low_implies_any_input_high: assert property (
        @(posedge clk) !Y |-> (A || B || C || D)
    );

endmodule