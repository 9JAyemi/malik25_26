module my_module_sva (
    input logic CLK,   // Sampling clock for assertions (RTL is purely combinational)
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic X
);
    // A low forces X low.
    check_a_low_forces_x0: assert property (
        @(posedge CLK) (A == 1'b0) |=> (X == 1'b0)
    );

    // If A is high and (B+C) >= D then X must be 1.
    check_t_ge_d_sets_x1: assert property (
        @(posedge CLK) ((A == 1'b1) && ((B + C) >= D)) |=> (X == 1'b1)
    );

    // If A is high and (B+C) < D then X equals ((E + (B + C)) >= D).
    check_else_path_exact: assert property (
        @(posedge CLK) ((A == 1'b1) && ((B + C) < D)) |=> (X == ((E + (B + C)) >= D))
    );

    // X can be 1 only when A is 1 and one of the comparisons is true.
    check_x1_only_when_conditions: assert property (
        @(posedge CLK) (X == 1'b1) |=> ((A == 1'b1) && ( ((B + C) >= D) || ((E + (B + C)) >= D) ))
    );

    // Full functional equivalence of X to the RTL logic.
    check_functional_equiv: assert property (
        @(posedge CLK) X == (A && ( ((B + C) >= D) || ((E + (B + C)) >= D) ))
    );

    // When D is 0 and A is 1, X must be 1.
    check_d_zero_implies_x1_when_a1: assert property (
        @(posedge CLK) ((A == 1'b1) && (D == 1'b0)) |=> (X == 1'b1)
    );
endmodule