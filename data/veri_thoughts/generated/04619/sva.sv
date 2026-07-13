module sky130_fd_sc_ms__o211a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // X equals the implemented OR-AND function.
    check_function_match: assert property (
        @(posedge clk) X == ((A1 | A2) & B1 & C1)
    );

    // B1 low forces the output low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> (X == 1'b0)
    );

    // C1 low forces the output low.
    check_c1_low_forces_x_low: assert property (
        @(posedge clk) !C1 |-> (X == 1'b0)
    );

    // Both A inputs low force the output low.
    check_a_inputs_low_force_x_low: assert property (
        @(posedge clk) (!A1 && !A2) |-> (X == 1'b0)
    );

    // A1 with both gating inputs high drives the output high.
    check_a1_path_drives_x_high: assert property (
        @(posedge clk) (A1 && B1 && C1) |-> (X == 1'b1)
    );

    // A2 with both gating inputs high drives the output high.
    check_a2_path_drives_x_high: assert property (
        @(posedge clk) (A2 && B1 && C1) |-> (X == 1'b1)
    );

    // High output requires both gating inputs and one A input high.
    check_x_high_implies_required_inputs: assert property (
        @(posedge clk) X |-> (B1 && C1 && (A1 || A2))
    );

endmodule