module add_sub_sva (
    input  logic        CLK,
    input  logic [2:0]  A,
    input  logic [2:0]  B,
    input  logic        C,
    input  logic [2:0]  Y
);
    // Reference computations (3-bit sized to match RTL behavior)
    logic [2:0] b_neg_ref;
    logic [2:0] add_ref;
    logic [2:0] sub_ref;
    logic [2:0] y_ref;

    assign b_neg_ref = ~B + 3'd1;
    assign add_ref   = A + B;
    assign sub_ref   = A + b_neg_ref;
    assign y_ref     = C ? sub_ref : add_ref;

    // Y always equals the muxed add/sub result.
    check_y_matches_spec: assert property (
        @(posedge CLK) (Y == y_ref)
    );

    // When C==0, Y equals A + B.
    check_y_add_when_c0: assert property (
        @(posedge CLK) (!C) |-> (Y == add_ref)
    );

    // When C==1, Y equals A + (~B + 1).
    check_y_sub_when_c1: assert property (
        @(posedge CLK) (C) |-> (Y == sub_ref)
    );

    // For subtraction mode, Y equals A - B (3-bit wraparound).
    check_y_sub_equiv_minus: assert property (
        @(posedge CLK) (C) |-> (Y == (A - B))
    );

    // If Y changes, at least one of A/B/C changed.
    check_y_change_implies_input_change: assert property (
        @(posedge CLK) $changed(Y) |-> ($changed(A) || $changed(B) || $changed(C))
    );

    // If B is zero, Y equals A regardless of C.
    check_b_zero_y_eq_a: assert property (
        @(posedge CLK) (B == 3'd0) |-> (Y == A)
    );

    // In subtraction mode, equal inputs yield zero.
    check_c1_equal_inputs_y_zero: assert property (
        @(posedge CLK) (C && (A == B)) |-> (Y == 3'd0)
    );

    // In subtraction mode, B==7 increments A by 1 (3-bit wrap).
    check_c1_b_max_incr: assert property (
        @(posedge CLK) (C && (B == 3'd7)) |-> (Y == (A + 3'd1))
    );

    // In addition mode, reversing with -B returns A: (Y + (~B + 1)) == A.
    check_c0_reverse_identity: assert property (
        @(posedge CLK) (!C) |-> ((Y + (~B + 3'd1)) == A)
    );

    // In subtraction mode, reversing with +B returns A: (Y + B) == A.
    check_c1_reverse_identity: assert property (
        @(posedge CLK) (C) |-> ((Y + B) == A)
    );
endmodule