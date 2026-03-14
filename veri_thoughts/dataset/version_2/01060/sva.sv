module and4_module_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    ///// Combinational AND truth /////
    // X equals the AND of all inputs and rails.
    check_and_function_equality: assert property (
        @(posedge A) X == (A & B & C & D & VPWR & VGND & VPB & VNB)
    );

    ///// Dominance of 0 /////
    // If any input/rail is 0, X must be 0.
    check_zero_when_any_input_zero: assert property (
        @(posedge A) ((A==1'b0) || (B==1'b0) || (C==1'b0) || (D==1'b0) ||
                      (VPWR==1'b0) || (VGND==1'b0) || (VPB==1'b0) || (VNB==1'b0))
                      |-> (X==1'b0)
    );

    ///// All-ones drives X high /////
    // If all inputs/rails are 1, X must be 1.
    check_one_when_all_inputs_one: assert property (
        @(posedge A) (A && B && C && D && VPWR && VGND && VPB && VNB) |-> (X==1'b1)
    );

    ///// High output implies all inputs high /////
    // If X is 1, then all inputs/rails are 1.
    check_one_implies_all_inputs_one: assert property (
        @(posedge A) (X==1'b1) |-> (A && B && C && D && VPWR && VGND && VPB && VNB)
    );
endmodule