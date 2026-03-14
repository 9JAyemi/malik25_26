module or4_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);
    // X equals A | B | C | ~D.
    check_functional_equivalence: assert property (
        @(posedge CLK) disable iff (1'b0) X == (A | B | C | ~D)
    );
    // D low forces X high in the same cycle.
    check_d_low_forces_x_high: assert property (
        @(posedge CLK) disable iff (1'b0) (D == 1'b0) |=> (X == 1'b1)
    );
    // A high forces X high in the same cycle.
    check_a_high_forces_x_high: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 1'b1) |=> (X == 1'b1)
    );
    // B high forces X high in the same cycle.
    check_b_high_forces_x_high: assert property (
        @(posedge CLK) disable iff (1'b0) (B == 1'b1) |=> (X == 1'b1)
    );
    // C high forces X high in the same cycle.
    check_c_high_forces_x_high: assert property (
        @(posedge CLK) disable iff (1'b0) (C == 1'b1) |=> (X == 1'b1)
    );
    // When A,B,C are low and D is high, X must be low.
    check_all_abclow_dhigh_forces_x_low: assert property (
        @(posedge CLK) disable iff (1'b0) (!A && !B && !C && (D == 1'b1)) |=> (X == 1'b0)
    );
    // When A,B,C are low, X equals ~D.
    check_abclow_x_eq_notd: assert property (
        @(posedge CLK) disable iff (1'b0) (!A && !B && !C) |=> (X == ~D)
    );
    // When D is high, X equals A|B|C.
    check_dhigh_x_eq_abc: assert property (
        @(posedge CLK) disable iff (1'b0) (D == 1'b1) |=> (X == (A | B | C))
    );
    // If X is low, then A,B,C are low and D is high.
    check_x_low_implies_inputs_inactive: assert property (
        @(posedge CLK) disable iff (1'b0) (X == 1'b0) |=> (!A && !B && !C && (D == 1'b1))
    );
    // If X is high, then at least one of A,B,C is high or D is low.
    check_x_high_implies_cause: assert property (
        @(posedge CLK) disable iff (1'b0) (X == 1'b1) |=> (A || B || C || !D)
    );
endmodule