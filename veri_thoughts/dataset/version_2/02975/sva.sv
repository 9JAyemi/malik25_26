module sky130_fd_sc_hdll__nand3_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C
);
    // Y equals the 3-input NAND of A, B, C (including X/Z semantics).
    check_nand3_function: assert property (
        @(posedge clk) (Y === ~(A & B & C))
    );

    // Y is LOW only when all inputs are HIGH.
    check_y0_only_when_all_high: assert property (
        @(posedge clk) (Y === 1'b0) |-> (A === 1'b1 && B === 1'b1 && C === 1'b1)
    );

    // Y HIGH implies at least one input is LOW.
    check_y1_implies_any_zero: assert property (
        @(posedge clk) (Y === 1'b1) |-> (A === 1'b0 || B === 1'b0 || C === 1'b0)
    );

    // A LOW forces Y HIGH regardless of other inputs.
    check_a_zero_forces_y_one: assert property (
        @(posedge clk) (A === 1'b0) |-> (Y === 1'b1)
    );

    // B LOW forces Y HIGH regardless of other inputs.
    check_b_zero_forces_y_one: assert property (
        @(posedge clk) (B === 1'b0) |-> (Y === 1'b1)
    );

    // C LOW forces Y HIGH regardless of other inputs.
    check_c_zero_forces_y_one: assert property (
        @(posedge clk) (C === 1'b0) |-> (Y === 1'b1)
    );

    // With all inputs known (0/1), Y must be known (not X/Z).
    check_known_inputs_imply_known_y: assert property (
        @(posedge clk) (! $isunknown({A,B,C})) |-> (! $isunknown(Y))
    );

    // Y is never high-impedance (buf is not tri-statable).
    check_y_never_z: assert property (
        @(posedge clk) (Y !== 1'bz)
    );

    // If inputs are stable across a cycle, Y must be stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(C)) |-> $stable(Y)
    );

    // If Y changes between cycles, at least one input must have changed.
    check_output_change_implies_input_change: assert property (
        @(posedge clk) $changed(Y) |-> ($changed(A) || $changed(B) || $changed(C))
    );
endmodule