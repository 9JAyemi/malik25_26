module and4_sva (
    input  logic CLK,
    input  logic A,
    input  logic B,
    input  logic C,
    input  logic D,
    input  logic Y
);
    // Y equals logical AND of all inputs.
    check_functional_equivalence: assert property (
        @(posedge CLK) Y == (A & B & C & D)
    );

    // If Y is HIGH, all inputs must be HIGH.
    check_Y_high_implies_all_inputs_high: assert property (
        @(posedge CLK) (Y == 1'b1) |-> ((A == 1'b1) && (B == 1'b1) && (C == 1'b1) && (D == 1'b1))
    );

    // If all inputs are HIGH, Y must be HIGH.
    check_all_inputs_high_implies_Y_high: assert property (
        @(posedge CLK) ((A == 1'b1) && (B == 1'b1) && (C == 1'b1) && (D == 1'b1)) |-> (Y == 1'b1)
    );

    // If A is LOW, Y must be LOW.
    check_A_zero_forces_Y_zero: assert property (
        @(posedge CLK) (A == 1'b0) |-> (Y == 1'b0)
    );

    // If B is LOW, Y must be LOW.
    check_B_zero_forces_Y_zero: assert property (
        @(posedge CLK) (B == 1'b0) |-> (Y == 1'b0)
    );

    // If C is LOW, Y must be LOW.
    check_C_zero_forces_Y_zero: assert property (
        @(posedge CLK) (C == 1'b0) |-> (Y == 1'b0)
    );

    // If D is LOW, Y must be LOW.
    check_D_zero_forces_Y_zero: assert property (
        @(posedge CLK) (D == 1'b0) |-> (Y == 1'b0)
    );

    // A rising Y requires all inputs HIGH at that time.
    check_rose_Y_requires_all_inputs_high: assert property (
        @(posedge CLK) $rose(Y) |-> ((A == 1'b1) && (B == 1'b1) && (C == 1'b1) && (D == 1'b1))
    );

    // A falling Y requires at least one input LOW at that time.
    check_fell_Y_requires_some_input_low: assert property (
        @(posedge CLK) $fell(Y) |-> ((A == 1'b0) || (B == 1'b0) || (C == 1'b0) || (D == 1'b0))
    );

    // If inputs are stable across a cycle, Y must be stable.
    check_Y_stable_if_inputs_stable: assert property (
        @(posedge CLK) $stable({A,B,C,D}) |-> $stable(Y)
    );
endmodule