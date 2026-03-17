module sky130_fd_sc_hd__o211a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // X matches the implemented O211 logic function.
    check_function_exact: assert property (
        @(posedge clk) X == (((A1 | A2) & B1) & C1)
    );

    // Low B1 forces the AND output low.
    check_b1_gates_output_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // Low C1 forces the AND output low.
    check_c1_gates_output_low: assert property (
        @(posedge clk) !C1 |-> !X
    );

    // With both OR inputs low, the output must be low.
    check_or_inputs_low_force_output_low: assert property (
        @(posedge clk) !(A1 | A2) |-> !X
    );

    // A1 can drive X high when both gating inputs are high.
    check_a1_path_drives_high: assert property (
        @(posedge clk) (A1 & B1 & C1) |-> X
    );

    // A2 can drive X high when both gating inputs are high.
    check_a2_path_drives_high: assert property (
        @(posedge clk) (A2 & B1 & C1) |-> X
    );

    // High X requires B1 to be high.
    check_output_high_implies_b1: assert property (
        @(posedge clk) X |-> B1
    );

    // High X requires C1 to be high.
    check_output_high_implies_c1: assert property (
        @(posedge clk) X |-> C1
    );

    // High X requires at least one OR input to be high.
    check_output_high_implies_or_term: assert property (
        @(posedge clk) X |-> (A1 | A2)
    );

endmodule