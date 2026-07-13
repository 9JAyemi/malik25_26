module sky130_fd_sc_hd__and4_assertions (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // X equals the AND of all four inputs.
    check_output_matches_and: assert property (
        @(posedge clk) X == (A & B & C & D)
    );

    // All four high inputs drive X high.
    check_all_high_drives_output_high: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b1) && (C == 1'b1) && (D == 1'b1)) |-> (X == 1'b1)
    );

    // A low forces X low.
    check_a_low_forces_output_low: assert property (
        @(posedge clk) (A == 1'b0) |-> (X == 1'b0)
    );

    // B low forces X low.
    check_b_low_forces_output_low: assert property (
        @(posedge clk) (B == 1'b0) |-> (X == 1'b0)
    );

    // C low forces X low.
    check_c_low_forces_output_low: assert property (
        @(posedge clk) (C == 1'b0) |-> (X == 1'b0)
    );

    // D low forces X low.
    check_d_low_forces_output_low: assert property (
        @(posedge clk) (D == 1'b0) |-> (X == 1'b0)
    );

    // A high X requires all four inputs high.
    check_output_high_requires_all_inputs_high: assert property (
        @(posedge clk) (X == 1'b1) |-> ((A == 1'b1) && (B == 1'b1) && (C == 1'b1) && (D == 1'b1))
    );

endmodule