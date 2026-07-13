module sky130_fd_sc_ls__a211o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);
    // X equals (A1 & A2) | B1 | C1.
    check_functional_equivalence: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        X === ((A1 & A2) | B1 | C1)
    );

    // If X is 0 then B1=0, C1=0, and (A1 & A2)=0.
    check_x_low_implies_inputs_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        (X === 1'b0) |-> ((B1 === 1'b0) && (C1 === 1'b0) && ((A1 & A2) === 1'b0))
    );

    // If B1 is 1 then X must be 1.
    check_b1_high_implies_x_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        (B1 === 1'b1) |-> (X === 1'b1)
    );

    // If C1 is 1 then X must be 1.
    check_c1_high_implies_x_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        (C1 === 1'b1) |-> (X === 1'b1)
    );

    // If (A1 & A2) is 1 then X must be 1.
    check_and_term_implies_x_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        ((A1 & A2) === 1'b1) |-> (X === 1'b1)
    );

    // When B1=0 and C1=0, X equals (A1 & A2).
    check_reduce_to_and_when_b1c1_zero: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        ((B1 === 1'b0) && (C1 === 1'b0)) |-> (X === (A1 & A2))
    );

    // When A1=0, X reduces to (B1 | C1).
    check_a1_zero_reduces_to_b1_or_c1: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        (A1 === 1'b0) |-> (X === (B1 | C1))
    );

    // When A2=0, X reduces to (B1 | C1).
    check_a2_zero_reduces_to_b1_or_c1: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        (A2 === 1'b0) |-> (X === (B1 | C1))
    );

    // If A1=0, B1=0, C1=0 then X must be 0.
    check_all_low_implies_x_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        ((A1 === 1'b0) && (B1 === 1'b0) && (C1 === 1'b0)) |-> (X === 1'b0)
    );

    // If either B1 or C1 is 1 then X must be 1.
    check_side_inputs_or_implies_x_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge C1 or negedge C1)
        ((B1 | C1) === 1'b1) |-> (X === 1'b1)
    );
endmodule