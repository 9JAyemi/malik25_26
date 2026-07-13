module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);
    // Analysis: no clock/reset; combinational; Y=1 if A1,A2,A3 all equal, else Y=B1.

    // Y must match the RTL ternary expression.
    check_y_matches_rtl_expr: assert property (
        @(posedge $global_clock) Y == ( ((A1 & A2 & A3) | (~A1 & ~A2 & ~A3)) ? 1'b1 : B1 )
    );

    // Y is 1 when A1,A2,A3 are all 1 or all 0.
    check_y_one_when_unanimous: assert property (
        @(posedge $global_clock) ((A1 & A2 & A3) || (~A1 & ~A2 & ~A3)) |-> (Y == 1'b1)
    );

    // When inputs are not unanimous, Y equals B1.
    check_y_equals_b1_when_not_unanimous: assert property (
        @(posedge $global_clock) !((A1 & A2 & A3) | (~A1 & ~A2 & ~A3)) |-> (Y == B1)
    );

    // Y==0 implies B1==0 and inputs are not unanimous.
    check_y_zero_implies_b1_zero_and_not_unanimous: assert property (
        @(posedge $global_clock) (Y == 1'b0) |-> ((B1 == 1'b0) && !((A1 & A2 & A3) | (~A1 & ~A2 & ~A3)))
    );

    // Y==1 implies B1==1 or inputs are unanimous.
    check_y_one_implies_cause: assert property (
        @(posedge $global_clock) (Y == 1'b1) |-> ((B1 == 1'b1) || (A1 & A2 & A3) || (~A1 & ~A2 & ~A3))
    );

    // B1==1 always forces Y==1.
    check_b1_one_forces_y_one: assert property (
        @(posedge $global_clock) (B1 == 1'b1) |-> (Y == 1'b1)
    );

    // When B1==0, Y equals the unanimity function of A1,A2,A3.
    check_b1_zero_implies_y_equals_unanimous: assert property (
        @(posedge $global_clock) (B1 == 1'b0) |-> (Y == ((A1 & A2 & A3) | (~A1 & ~A2 & ~A3)))
    );

    // Y differs from B1 only when inputs are unanimous and B1 is 0.
    check_y_differs_from_b1_only_when_unanimous_b1_zero: assert property (
        @(posedge $global_clock) (Y != B1) |-> (((A1 & A2 & A3) || (~A1 & ~A2 & ~A3)) && (B1 == 1'b0) && (Y == 1'b1))
    );

    // If not unanimous and B1==1, then Y==1.
    check_not_unanimous_b1_one_y_one: assert property (
        @(posedge $global_clock) (!((A1 & A2 & A3) | (~A1 & ~A2 & ~A3)) && (B1 == 1'b1)) |-> (Y == 1'b1)
    );

    // If not unanimous and B1==0, then Y==0.
    check_not_unanimous_b1_zero_y_zero: assert property (
        @(posedge $global_clock) (!((A1 & A2 & A3) | (~A1 & ~A2 & ~A3)) && (B1 == 1'b0)) |-> (Y == 1'b0)
    );
endmodule