module sky130_fd_sc_hdll__nand2b_sva (
    input logic CLK,
    input logic RESETn,
    input logic Y,
    input logic A_N,
    input logic B
);
    // Y must equal (~B) | A_N (gate-level functional equivalence).
    check_function_equation_or: assert property (
        @(posedge CLK) disable iff (!RESETn) Y == ((~B) | A_N)
    );

    // Y must equal ~(B & ~A_N) (De Morgan equivalent form).
    check_function_equation_demorgan: assert property (
        @(posedge CLK) disable iff (!RESETn) Y == ~(B & ~A_N)
    );

    // If B is 0, Y must be 1 (since ~B is 1).
    check_y_high_when_b_low: assert property (
        @(posedge CLK) disable iff (!RESETn) (B == 1'b0) |-> (Y == 1'b1)
    );

    // If A_N is 1, Y must be 1 (OR with 1 drives 1).
    check_y_high_when_a_n_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (A_N == 1'b1) |-> (Y == 1'b1)
    );

    // If B is 1 and A_N is 0, Y must be 0 (only case that drives 0).
    check_y_low_when_b_high_a_n_low: assert property (
        @(posedge CLK) disable iff (!RESETn) ((B == 1'b1) && (A_N == 1'b0)) |-> (Y == 1'b0)
    );

    // If Y is 0, then B must be 1 and A_N must be 0 (unique low condition).
    check_y_low_implies_inputs: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y == 1'b0) |-> ((B == 1'b1) && (A_N == 1'b0))
    );

    // If Y is 1, then either B is 0 or A_N is 1.
    check_y_high_implies_inputs: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y == 1'b1) |-> ((B == 1'b0) || (A_N == 1'b1))
    );
endmodule