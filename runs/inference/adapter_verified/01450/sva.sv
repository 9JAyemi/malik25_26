module sky130_fd_sc_ls__o32ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);

// Y matches the implemented NOR/OR/BUF function.
    check_function_equivalence: assert property (
        @(posedge clk) Y == ((~(A1 | A2 | A3)) | (~(B1 | B2)))
    );

// A high A-3 input forces Y low.
    check_a3_forces_low: assert property (
        @(posedge clk) A3 |-> !Y
    );

// A high A-2 input forces Y low.
    check_a2_forces_low: assert property (
        @(posedge clk) A2 |-> !Y
    );

// A high A-1 input forces Y low.
    check_a1_forces_low: assert property (
        @(posedge clk) A1 |-> !Y
    );

// A high B-1 input forces Y low.
    check_b1_forces_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

// A high B-2 input forces Y low.
    check_b2_forces_low: assert property (
        @(posedge clk) B2 |-> !Y
    );

// All A inputs low with both B inputs low drive Y high.
    check_all_inputs_low_drive_high: assert property (
        @(posedge clk) (!A1 && !A2 && !A3 && !B1 && !B2) |-> Y
    );

// A high Y requires all A inputs low and both B inputs low.
    check_y_high_requires_all_inputs_low: assert property (
        @(posedge clk) Y |-> (!A1 && !A2 && !A3 && !B1 && !B2)
    );

endmodule
