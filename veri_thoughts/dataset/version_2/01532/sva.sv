module five_to_one_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic [1:0] B,
    input logic X
);
    // X matches the RTL boolean equation exactly.
    check_x_definition: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge X or negedge X)
        X == ((A1 == 1'b1) && (A2 == 1'b0) && (A3 == 1'b1) && ((B == 2'b10) || (B == 2'b11)))
    );

    // If X is 1, inputs must satisfy the enable condition.
    check_x_high_implies_inputs: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge X or negedge X)
        (X == 1'b1) |-> ((A1 == 1'b1) && (A2 == 1'b0) && (A3 == 1'b1) && ((B == 2'b10) || (B == 2'b11)))
    );

    // A1 low forces X low.
    check_a1_low_blocks_x: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge X or negedge X)
        (A1 == 1'b0) |-> (X == 1'b0)
    );

    // A2 high forces X low.
    check_a2_high_blocks_x: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge X or negedge X)
        (A2 == 1'b1) |-> (X == 1'b0)
    );

    // A3 low forces X low.
    check_a3_low_blocks_x: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge X or negedge X)
        (A3 == 1'b0) |-> (X == 1'b0)
    );

    // B[1] low forces X low (B must be 2'b10 or 2'b11).
    check_b_msb_low_blocks_x: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge X or negedge X)
        (B[1] == 1'b0) |-> (X == 1'b0)
    );

    // Exact enable case with B==2'b10 drives X high.
    check_enable_case_b10_sets_x: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge X or negedge X)
        ((A1 == 1'b1) && (A2 == 1'b0) && (A3 == 1'b1) && (B == 2'b10)) |-> (X == 1'b1)
    );

    // Exact enable case with B==2'b11 drives X high.
    check_enable_case_b11_sets_x: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge X or negedge X)
        ((A1 == 1'b1) && (A2 == 1'b0) && (A3 == 1'b1) && (B == 2'b11)) |-> (X == 1'b1)
    );

    // If B is not 2'b10 or 2'b11, X must be low.
    check_invalid_b_values_block_x: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge A3 or negedge A3 or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge X or negedge X)
        !((B == 2'b10) || (B == 2'b11)) |-> (X == 1'b0)
    );
endmodule