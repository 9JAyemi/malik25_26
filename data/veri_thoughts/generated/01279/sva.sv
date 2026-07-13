module my_module_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // X equals the implemented boolean expression.
    check_function_equation: assert property (
        @(posedge B2) X == ((A1 & (A2 & A3)) | ((~A1) & B1 & (B2 | VPWR)) | ((~A1) & (~B1) & (VPB ^ VNB)))
    );

    // When A1 is HIGH, X equals A2 & A3.
    check_A1_high_path: assert property (
        @(posedge B2) A1 |-> (X == (A2 & A3))
    );

    // When A1 is LOW and B1 is HIGH, X equals B2 | VPWR.
    check_A1_low_B1_high_path: assert property (
        @(posedge B2) (~A1 & B1) |-> (X == (B2 | VPWR))
    );

    // When A1 is LOW and B1 is LOW, X equals VPB ^ VNB.
    check_A1_low_B1_low_path: assert property (
        @(posedge B2) (~A1 & ~B1) |-> (X == (VPB ^ VNB))
    );

    // If A1=1 and A2=1 and A3=1, then X must be 1.
    check_A1_high_all_ones_implies_X1: assert property (
        @(posedge B2) (A1 & A2 & A3) |-> (X == 1'b1)
    );

    // If A1=1 and A2=0, then X must be 0.
    check_A1_high_A2_zero_implies_X0: assert property (
        @(posedge B2) (A1 & ~A2) |-> (X == 1'b0)
    );

    // If A1=1 and A3=0, then X must be 0.
    check_A1_high_A3_zero_implies_X0: assert property (
        @(posedge B2) (A1 & ~A3) |-> (X == 1'b0)
    );

    // If A1=0, B1=1, and B2=1, then X must be 1.
    check_else_path_B2_one_implies_X1: assert property (
        @(posedge B2) (~A1 & B1 & B2) |-> (X == 1'b1)
    );

    // If A1=0, B1=1, and VPWR=1, then X must be 1.
    check_else_path_VPWR_one_implies_X1: assert property (
        @(posedge B2) (~A1 & B1 & VPWR) |-> (X == 1'b1)
    );

    // If A1=0, B1=1, B2=0, and VPWR=0, then X must be 0.
    check_else_path_zero_inputs_implies_X0: assert property (
        @(posedge B2) (~A1 & B1 & ~B2 & ~VPWR) |-> (X == 1'b0)
    );

    // If A1=0, B1=0, and VPB==VNB, then X must be 0.
    check_xor_path_equal_inputs_implies_X0: assert property (
        @(posedge B2) (~A1 & ~B1 & (VPB ~^ VNB)) |-> (X == 1'b0)
    );

    // If A1=0, B1=0, and VPB!=VNB, then X must be 1.
    check_xor_path_unequal_inputs_implies_X1: assert property (
        @(posedge B2) (~A1 & ~B1 & (VPB ^ VNB)) |-> (X == 1'b1)
    );
endmodule