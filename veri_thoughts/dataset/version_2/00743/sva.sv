module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // Analysis: no clock/reset in RTL; pure combinational OR->NAND->BUF; sample on edges of A1/A2/A3/B1.
    // Functional: Y = ~(B1 & (A1 | A2 | A3)).

    // Y equals NAND(B1, OR(A1,A2,A3)).
    check_y_functional_equivalence: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1)
            (Y == ~(B1 & (A1 | A2 | A3)))
    );

    // If B1 is 0 then Y must be 1.
    check_y_high_when_b1_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1)
            (!B1) |-> (Y == 1'b1)
    );

    // If B1 is 1 and any A is 1 then Y must be 0.
    check_y_low_when_b1_and_any_a_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1)
            (B1 && (A1 || A2 || A3)) |-> (Y == 1'b0)
    );

    // If B1 is 1 and all A are 0 then Y must be 1.
    check_y_high_when_b1_and_all_a_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1)
            (B1 && !A1 && !A2 && !A3) |-> (Y == 1'b1)
    );

    // If Y is 0 then B1 must be 1 and some A must be 1.
    check_y_low_implication_inputs: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1)
            (Y == 1'b0) |-> (B1 && (A1 || A2 || A3))
    );

    // If Y is 1 then either B1 is 0 or all A are 0.
    check_y_high_implication_inputs: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1)
            (Y == 1'b1) |-> (!B1 || (!A1 && !A2 && !A3))
    );

    // If all A are 0 then Y must be 1 (independent of B1).
    check_y_high_when_all_a_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1)
            (!A1 && !A2 && !A3) |-> (Y == 1'b1)
    );

    // If B1 and all A are 1 then Y must be 0.
    check_y_low_when_all_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B1 or negedge B1)
            (B1 && A1 && A2 && A3) |-> (Y == 1'b0)
    );

endmodule