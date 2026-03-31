module and_gate_4_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    input logic Y
);

// Y must equal the AND of all five inputs.
    check_y_matches_and_function: assert property (
        @(posedge clk) Y == (A1 & A2 & A3 & B1 & C1)
    );

// A low on A1 forces Y low.
    check_a1_low_forces_y_low: assert property (
        @(posedge clk) !A1 |-> !Y
    );

// A low on A2 forces Y low.
    check_a2_low_forces_y_low: assert property (
        @(posedge clk) !A2 |-> !Y
    );

// A low on A3 forces Y low.
    check_a3_low_forces_y_low: assert property (
        @(posedge clk) !A3 |-> !Y
    );

// A low on B1 forces Y low.
    check_b1_low_forces_y_low: assert property (
        @(posedge clk) !B1 |-> !Y
    );

// A low on C1 forces Y low.
    check_c1_low_forces_y_low: assert property (
        @(posedge clk) !C1 |-> !Y
    );

// All five high inputs drive Y high.
    check_all_high_drives_y_high: assert property (
        @(posedge clk) (A1 & A2 & A3 & B1 & C1) |-> Y
    );

endmodule
