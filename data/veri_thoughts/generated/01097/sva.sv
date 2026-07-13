module majority_gate_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);
    // Y equals the OR of all pairwise ANDs of A,B,C,D.
    check_y_equation: assert property (
        @(posedge CLK) Y == ((A & B) | (A & C) | (A & D) | (B & C) | (B & D) | (C & D))
    );

    // If A and B are HIGH together, Y must be HIGH.
    pair_AB_implies_Y: assert property (
        @(posedge CLK) (A & B) |-> Y
    );

    // If A and C are HIGH together, Y must be HIGH.
    pair_AC_implies_Y: assert property (
        @(posedge CLK) (A & C) |-> Y
    );

    // If A and D are HIGH together, Y must be HIGH.
    pair_AD_implies_Y: assert property (
        @(posedge CLK) (A & D) |-> Y
    );

    // If B and C are HIGH together, Y must be HIGH.
    pair_BC_implies_Y: assert property (
        @(posedge CLK) (B & C) |-> Y
    );

    // If B and D are HIGH together, Y must be HIGH.
    pair_BD_implies_Y: assert property (
        @(posedge CLK) (B & D) |-> Y
    );

    // If C and D are HIGH together, Y must be HIGH.
    pair_CD_implies_Y: assert property (
        @(posedge CLK) (C & D) |-> Y
    );

    // When all inputs are LOW, Y must be LOW.
    all_zero_implies_zero: assert property (
        @(posedge CLK) !(A | B | C | D) |-> !Y
    );

    // When exactly one input is HIGH, Y must be LOW.
    onehot_implies_zero: assert property (
        @(posedge CLK) $onehot({A,B,C,D}) |-> !Y
    );

    // When all inputs are HIGH, Y must be HIGH.
    all_one_implies_one: assert property (
        @(posedge CLK) (A & B & C & D) |-> Y
    );
endmodule