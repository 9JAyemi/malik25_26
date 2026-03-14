module multi_input_output_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C,
    input logic [7:0] D,
    input logic [7:0] E,
    input logic [7:0] F,
    input logic [7:0] G,
    input logic [7:0] H,
    input logic [7:0] Y
);

    ///// Functional correctness /////
    // Y equals (A+B)-(C+D)+(E+F)-(G+H) with 8-bit wrap.
    check_y_definition: assert property (
        @(posedge A[0]) Y == (A + B) - (C + D) + (E + F) - (G + H)
    );

    // All inputs zero yields Y=0.
    check_y_all_zero_input: assert property (
        @(posedge A[0]) ((A==8'h00)&&(B==8'h00)&&(C==8'h00)&&(D==8'h00)&&(E==8'h00)&&(F==8'h00)&&(G==8'h00)&&(H==8'h00))
        |-> (Y==8'h00)
    );

    // If B..H are zero, Y passes A.
    check_y_passthrough_A_when_others_zero: assert property (
        @(posedge A[0]) ((B==8'h00)&&(C==8'h00)&&(D==8'h00)&&(E==8'h00)&&(F==8'h00)&&(G==8'h00)&&(H==8'h00))
        |-> (Y==A)
    );

    // If pairwise inputs match (A=C,B=D,E=G,F=H), Y is zero.
    check_y_zero_when_pairs_equal: assert property (
        @(posedge A[0]) ((A==C)&&(B==D)&&(E==G)&&(F==H))
        |-> (Y==8'h00)
    );

    // If E=F=G=H=0, Y=(A+B)-(C+D).
    check_y_when_EFGH_zero: assert property (
        @(posedge A[0]) ((E==8'h00)&&(F==8'h00)&&(G==8'h00)&&(H==8'h00))
        |-> (Y == (A + B) - (C + D))
    );

    // If G=H=0, Y=(A+B)-(C+D)+(E+F).
    check_y_when_GH_zero: assert property (
        @(posedge A[0]) ((G==8'h00)&&(H==8'h00))
        |-> (Y == (A + B) - (C + D) + (E + F))
    );

    // If A=B=C=D=0, Y=(E+F)-(G+H).
    check_y_when_ABCD_zero: assert property (
        @(posedge A[0]) ((A==8'h00)&&(B==8'h00)&&(C==8'h00)&&(D==8'h00))
        |-> (Y == (E + F) - (G + H))
    );

    ///// Algebraic cancellation checks (mod-256 arithmetic) /////
    // Adding back (G+H) cancels the final subtraction.
    check_cancel_gh_addback: assert property (
        @(posedge A[0]) (Y + (G + H)) == ( (A + B) - (C + D) + (E + F) )
    );

    // Adding back (G+H) then subtracting (E+F) cancels the last two pairs.
    check_cancel_gh_then_ef: assert property (
        @(posedge A[0]) ((Y + (G + H)) - (E + F)) == ( (A + B) - (C + D) )
    );

    // After canceling GH and EF and adding (C+D), recover (A+B).
    check_recover_ab: assert property (
        @(posedge A[0]) (((Y + (G + H)) - (E + F)) + (C + D)) == (A + B)
    );

endmodule