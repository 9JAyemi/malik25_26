module and_gate_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // Y must equal the AND of all five inputs.
    check_y_matches_and_function: assert property (
        @(posedge clk) Y == (A1 & A2 & B1 & C1 & D1)
    );

    // All inputs high must drive Y high.
    check_all_inputs_high_drive_y_high: assert property (
        @(posedge clk) (A1 & A2 & B1 & C1 & D1) |-> Y
    );

    // A low A1 input must force Y low.
    check_a1_low_forces_y_low: assert property (
        @(posedge clk) !A1 |-> !Y
    );

    // A low A2 input must force Y low.
    check_a2_low_forces_y_low: assert property (
        @(posedge clk) !A2 |-> !Y
    );

    // A low B1 input must force Y low.
    check_b1_low_forces_y_low: assert property (
        @(posedge clk) !B1 |-> !Y
    );

    // A low C1 input must force Y low.
    check_c1_low_forces_y_low: assert property (
        @(posedge clk) !C1 |-> !Y
    );

    // A low D1 input must force Y low.
    check_d1_low_forces_y_low: assert property (
        @(posedge clk) !D1 |-> !Y
    );

    // A high Y requires all inputs to be high.
    check_y_high_requires_all_inputs_high: assert property (
        @(posedge clk) Y |-> (A1 & A2 & B1 & C1 & D1)
    );

endmodule