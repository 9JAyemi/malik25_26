module sky130_fd_sc_ls__or4b_sva (
    input logic CLK,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N
);
    // A high forces X high.
    force_x_high_when_a_high: assert property (
        @(posedge CLK) (A == 1'b1) |-> (X == 1'b1)
    );
    // B high forces X high.
    force_x_high_when_b_high: assert property (
        @(posedge CLK) (B == 1'b1) |-> (X == 1'b1)
    );
    // C high forces X high.
    force_x_high_when_c_high: assert property (
        @(posedge CLK) (C == 1'b1) |-> (X == 1'b1)
    );
    // D_N low forces X high.
    force_x_high_when_dn_low: assert property (
        @(posedge CLK) (D_N == 1'b0) |-> (X == 1'b1)
    );
    // All-neutral inputs drive X low.
    force_x_low_when_all_neutral: assert property (
        @(posedge CLK) ((A == 1'b0) && (B == 1'b0) && (C == 1'b0) && (D_N == 1'b1)) |-> (X == 1'b0)
    );
    // X low implies all inputs neutral.
    x_low_implies_all_neutral: assert property (
        @(posedge CLK) (X == 1'b0) |-> ((A == 1'b0) && (B == 1'b0) && (C == 1'b0) && (D_N == 1'b1))
    );
    // X high implies at least one asserted (A/B/C) or D_N low.
    x_high_implies_any_input_true: assert property (
        @(posedge CLK) (X == 1'b1) |-> ((A == 1'b1) || (B == 1'b1) || (C == 1'b1) || (D_N == 1'b0))
    );
    // If inputs are stable, X is stable.
    x_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable({A,B,C,D_N}) |-> $stable(X)
    );
    // X cannot change without some input changing.
    output_change_requires_input_change: assert property (
        @(posedge CLK) $changed(X) |-> $changed({A,B,C,D_N})
    );
    // With B=0,C=0,D_N=1, X equals A.
    x_equals_a_when_b0_c0_dn1: assert property (
        @(posedge CLK) ((B == 1'b0) && (C == 1'b0) && (D_N == 1'b1)) |-> (X == A)
    );
    // With A=0,B=0,C=0, X equals !D_N.
    x_equals_notdn_when_a0_b0_c0: assert property (
        @(posedge CLK) ((A == 1'b0) && (B == 1'b0) && (C == 1'b0)) |-> (X == !D_N)
    );
    // When all inputs are known, X equals (!D_N) OR A OR B OR C.
    truth_table_when_inputs_known: assert property (
        @(posedge CLK) (!$isunknown({A,B,C,D_N})) |-> (X == ((!D_N) || A || B || C))
    );
endmodule