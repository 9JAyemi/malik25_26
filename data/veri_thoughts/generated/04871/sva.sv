module nor_gate_sva(
    input logic clk,
    input logic A,
    input logic B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic Y
);

    // Y matches the implemented combinational equation.
    check_output_matches_equation: assert property (
        @(posedge clk) Y == (~((~A) & (~B)))
    );

    // A high drives Y high.
    check_a_high_drives_output_high: assert property (
        @(posedge clk) A |-> Y
    );

    // B high drives Y high.
    check_b_high_drives_output_high: assert property (
        @(posedge clk) B |-> Y
    );

    // Both inputs low drive Y low.
    check_both_inputs_low_drive_output_low: assert property (
        @(posedge clk) (!A && !B) |-> !Y
    );

    // A low output means both inputs are low.
    check_output_low_requires_both_inputs_low: assert property (
        @(posedge clk) !Y |-> (!A && !B)
    );

endmodule