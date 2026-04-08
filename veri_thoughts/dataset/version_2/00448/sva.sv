module four_input_nand_sva (
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D,
    input logic Y,
    input logic VPWR,
    input logic VGND
);

    // No RTL clock or reset; the design is purely combinational.
    // The cascaded nand4bb instances reduce to Y = A_N & B_N & C & D.

    // The top-level output matches the reduced Boolean function.
    check_function_equivalence: assert property (
        @($global_clock) Y == (A_N & B_N & C & D)
    );

    // All four inputs high drives the output high.
    check_all_inputs_high_drive_output_high: assert property (
        @($global_clock) (A_N && B_N && C && D) |-> Y
    );

    // Any low input forces the output low.
    check_any_input_low_forces_output_low: assert property (
        @($global_clock) (!A_N || !B_N || !C || !D) |-> !Y
    );

    // A high output requires all four inputs to be high.
    check_output_high_requires_all_inputs_high: assert property (
        @($global_clock) Y |-> (A_N && B_N && C && D)
    );

    // A low output means at least one input is low.
    check_output_low_requires_some_input_low: assert property (
        @($global_clock) !Y |-> (!A_N || !B_N || !C || !D)
    );

endmodule