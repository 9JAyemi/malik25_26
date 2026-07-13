module my_or4b_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N
);
    // X equals A|B|C|~D_N
    check_function_equation: assert property (
        @(posedge clk) X == (A | B | C | ~D_N)
    );

    // D_N low forces X high
    check_dn_low_forces_x_high: assert property (
        @(posedge clk) (D_N == 1'b0) |-> (X == 1'b1)
    );

    // A high forces X high
    check_a_high_forces_x_high: assert property (
        @(posedge clk) (A == 1'b1) |-> (X == 1'b1)
    );

    // B high forces X high
    check_b_high_forces_x_high: assert property (
        @(posedge clk) (B == 1'b1) |-> (X == 1'b1)
    );

    // C high forces X high
    check_c_high_forces_x_high: assert property (
        @(posedge clk) (C == 1'b1) |-> (X == 1'b1)
    );

    // All inputs inactive (A=B=C=0, D_N=1) forces X low
    check_all_inactive_forces_x_low: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b0) && (C == 1'b0) && (D_N == 1'b1)) |-> (X == 1'b0)
    );

    // X low implies A=B=C=0 and D_N=1
    check_x_low_implies_all_inactive: assert property (
        @(posedge clk) (X == 1'b0) |-> ((A == 1'b0) && (B == 1'b0) && (C == 1'b0) && (D_N == 1'b1))
    );

    // X high implies at least one of A,B,C is high or D_N is low
    check_x_high_implies_some_active: assert property (
        @(posedge clk) (X == 1'b1) |-> ((A == 1'b1) || (B == 1'b1) || (C == 1'b1) || (D_N == 1'b0))
    );

    // With D_N high, X equals A|B|C
    check_reduction_when_dn_high: assert property (
        @(posedge clk) (D_N == 1'b1) |-> (X == (A | B | C))
    );

    // With A=B=C=0, X equals ~D_N
    check_reduction_when_abc_low: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b0) && (C == 1'b0)) |-> (X == ~D_N)
    );
endmodule