module and_gate_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y,
    input logic VPWR,
    input logic VGND,
    input logic clk
);

    // Y must equal the AND of all four data inputs.
    check_output_equation: assert property (
        @(posedge clk) Y == (A & B & C & D)
    );

    // All four HIGH inputs must drive Y HIGH.
    check_all_inputs_high_drive_output_high: assert property (
        @(posedge clk) (A & B & C & D) |-> Y
    );

    // A HIGH Y requires all four data inputs to be HIGH.
    check_output_high_requires_all_inputs_high: assert property (
        @(posedge clk) Y |-> (A & B & C & D)
    );

    // Any LOW data input must force Y LOW.
    check_any_low_input_forces_output_low: assert property (
        @(posedge clk) (!A || !B || !C || !D) |-> !Y
    );

endmodule