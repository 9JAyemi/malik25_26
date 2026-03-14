module MUX21_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic Sel,
    input logic Z
);
    // Z equals selected input based on Sel each cycle.
    check_mux_function: assert property (
        @(posedge CLK) Z == (Sel ? B : A)
    );

    // When Sel is 0, Z must equal A.
    check_sel0_mapping: assert property (
        @(posedge CLK) (Sel == 1'b0) |-> (Z == A)
    );

    // When Sel is 1, Z must equal B.
    check_sel1_mapping: assert property (
        @(posedge CLK) (Sel == 1'b1) |-> (Z == B)
    );

    // If A, B, and Sel are stable, Z must be stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable(A) && $stable(B) && $stable(Sel) |-> $stable(Z)
    );

    // If Sel stays 0 and A changes across cycles, Z must change.
    check_a_change_propagates_when_sel0: assert property (
        @(posedge CLK) (Sel == 1'b0) && $stable(Sel) && !$stable(A) |-> !$stable(Z)
    );

    // If Sel stays 1 and B changes across cycles, Z must change.
    check_b_change_propagates_when_sel1: assert property (
        @(posedge CLK) (Sel == 1'b1) && $stable(Sel) && !$stable(B) |-> !$stable(Z)
    );

    // If Sel stays 0 and Z changes across cycles, A must have changed.
    check_z_change_implies_a_change_when_sel0: assert property (
        @(posedge CLK) (Sel == 1'b0) && $stable(Sel) && !$stable(Z) |-> !$stable(A)
    );

    // If Sel stays 1 and Z changes across cycles, B must have changed.
    check_z_change_implies_b_change_when_sel1: assert property (
        @(posedge CLK) (Sel == 1'b1) && $stable(Sel) && !$stable(Z) |-> !$stable(B)
    );

    // On Sel rising edge, Z reflects B in the same cycle.
    check_rose_sel_selects_B: assert property (
        @(posedge CLK) $rose(Sel) |-> (Z == B)
    );

    // On Sel falling edge, Z reflects A in the same cycle.
    check_fell_sel_selects_A: assert property (
        @(posedge CLK) $fell(Sel) |-> (Z == A)
    );
endmodule