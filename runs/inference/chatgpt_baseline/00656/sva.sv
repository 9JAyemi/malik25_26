module or3_4_custom_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C
);
    // Purely combinational 3-input OR: X = A | B | C; no clock or reset present.

    // X must equal A|B|C whenever A toggles.
    check_or_equation_on_A_edges: assert property (
        @(posedge A or negedge A) X === (A | B | C)
    );

    // X must equal A|B|C whenever B toggles.
    check_or_equation_on_B_edges: assert property (
        @(posedge B or negedge B) X === (A | B | C)
    );

    // X must equal A|B|C whenever C toggles.
    check_or_equation_on_C_edges: assert property (
        @(posedge C or negedge C) X === (A | B | C)
    );

    // When X falls, all inputs must be LOW.
    check_negedge_X_requires_all_inputs_low: assert property (
        @(negedge X) (!A && !B && !C)
    );

    // When A rises, X must be HIGH.
    check_posedge_A_forces_X_high: assert property (
        @(posedge A) (X == 1'b1)
    );

    // When B rises, X must be HIGH.
    check_posedge_B_forces_X_high: assert property (
        @(posedge B) (X == 1'b1)
    );

    // When C rises, X must be HIGH.
    check_posedge_C_forces_X_high: assert property (
        @(posedge C) (X == 1'b1)
    );

    // When A falls and others are LOW, X must be LOW.
    check_negedge_A_drops_X_when_others_low: assert property (
        @(negedge A) (!B && !C) |-> (X == 1'b0)
    );

    // When B falls and others are LOW, X must be LOW.
    check_negedge_B_drops_X_when_others_low: assert property (
        @(negedge B) (!A && !C) |-> (X == 1'b0)
    );

    // When C falls and others are LOW, X must be LOW.
    check_negedge_C_drops_X_when_others_low: assert property (
        @(negedge C) (!A && !B) |-> (X == 1'b0)
    );

endmodule