module nand3_gate_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Y
);
    ///// Combinational NAND behavior sampled on A's posedge /////
    // Y equals the 3-input NAND of A, B, and C.
    check_nand_function: assert property (
        @(posedge A) Y == ~(A & B & C)
    );

    // If any input is 0, Y must be 1.
    check_any_input_low_implies_y_high: assert property (
        @(posedge A) (!A || !B || !C) |-> (Y == 1'b1)
    );

    // Y can be 0 only when all inputs are 1.
    check_y_low_only_when_all_inputs_high: assert property (
        @(posedge A) (Y == 1'b0) |-> (A && B && C)
    );

    // When B and C are 1 and Y was 1, a rising A causes Y to fall.
    check_y_falls_when_a_rises_with_bc_high: assert property (
        @(posedge A) (B && C && $past(Y) == 1'b1) |-> $fell(Y)
    );

    // When either B or C is 0, a rising A leaves Y high.
    check_y_stays_high_when_bc_not_both_high_on_a_rise: assert property (
        @(posedge A) ((!B || !C)) |-> (Y == 1'b1)
    );
endmodule