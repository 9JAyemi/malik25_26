module sky130_fd_sc_ls__a32o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);
    // Analysis: no clock/reset; pure combinational; X = (A1 & A2 & A3) | (B1 & B2).

    // Check functional equivalence on A1 rising edge.
    check_func_on_A1_posedge: assert property (
        @(posedge A1) 1'b1 |-> ##0 (X == ((A1 & A2 & A3) | (B1 & B2)))
    );

    // Check functional equivalence on A1 falling edge.
    check_func_on_A1_negedge: assert property (
        @(negedge A1) 1'b1 |-> ##0 (X == ((A1 & A2 & A3) | (B1 & B2)))
    );

    // Check functional equivalence on A2 rising edge.
    check_func_on_A2_posedge: assert property (
        @(posedge A2) 1'b1 |-> ##0 (X == ((A1 & A2 & A3) | (B1 & B2)))
    );

    // Check functional equivalence on A2 falling edge.
    check_func_on_A2_negedge: assert property (
        @(negedge A2) 1'b1 |-> ##0 (X == ((A1 & A2 & A3) | (B1 & B2)))
    );

    // Check functional equivalence on A3 rising edge.
    check_func_on_A3_posedge: assert property (
        @(posedge A3) 1'b1 |-> ##0 (X == ((A1 & A2 & A3) | (B1 & B2)))
    );

    // Check functional equivalence on A3 falling edge.
    check_func_on_A3_negedge: assert property (
        @(negedge A3) 1'b1 |-> ##0 (X == ((A1 & A2 & A3) | (B1 & B2)))
    );

    // Check functional equivalence on B1 rising edge.
    check_func_on_B1_posedge: assert property (
        @(posedge B1) 1'b1 |-> ##0 (X == ((A1 & A2 & A3) | (B1 & B2)))
    );

    // Check functional equivalence on B1 falling edge.
    check_func_on_B1_negedge: assert property (
        @(negedge B1) 1'b1 |-> ##0 (X == ((A1 & A2 & A3) | (B1 & B2)))
    );

    // Check functional equivalence on B2 rising edge.
    check_func_on_B2_posedge: assert property (
        @(posedge B2) 1'b1 |-> ##0 (X == ((A1 & A2 & A3) | (B1 & B2)))
    );

    // Check functional equivalence on B2 falling edge.
    check_func_on_B2_negedge: assert property (
        @(negedge B2) 1'b1 |-> ##0 (X == ((A1 & A2 & A3) | (B1 & B2)))
    );

    // Rising edge on X only when function is 1.
    check_X_rise_implies_func1: assert property (
        @(posedge X) 1'b1 |-> ##0 (((A1 & A2 & A3) | (B1 & B2)) == 1'b1)
    );

    // Falling edge on X only when function is 0.
    check_X_fall_implies_func0: assert property (
        @(negedge X) 1'b1 |-> ##0 (((A1 & A2 & A3) | (B1 & B2)) == 1'b0)
    );

endmodule