module my_logic_sva (
    input logic CLK,        // No clock/reset in RTL; sample combinational logic on this external clock.
    input logic A1,
    input logic A2,
    input logic A3,
    input logic [1:0] B,
    input logic Y
);

    ///// Combinational function checks /////
    // Y equals the OR of A1,A2,A3,B[1],B[0].
    check_y_is_or_of_all: assert property (
        @(posedge CLK) Y == (A1 || A2 || A3 || B[1] || B[0])
    );

    // When any A is 1, Y must be 1.
    check_y_one_when_any_A: assert property (
        @(posedge CLK) (A1 || A2 || A3) |-> (Y == 1'b1)
    );

    // When all A are 0, Y equals OR of B.
    check_y_uses_B_when_As_zero: assert property (
        @(posedge CLK) (!A1 && !A2 && !A3) |-> (Y == (B[1] || B[0]))
    );

    // Y is 0 only when all inputs are 0.
    check_y_zero_only_when_all_zero: assert property (
        @(posedge CLK) (Y == 1'b0) |-> (!A1 && !A2 && !A3 && (B[1] == 1'b0) && (B[0] == 1'b0))
    );

    // With all A=0 and B!=0, Y must be 1.
    check_y_one_when_B_nonzero_and_As_zero: assert property (
        @(posedge CLK) (!A1 && !A2 && !A3 && (B != 2'b00)) |-> (Y == 1'b1)
    );

    // With all inputs 0, Y must be 0.
    check_y_zero_when_all_inputs_zero: assert property (
        @(posedge CLK) (!A1 && !A2 && !A3 && (B == 2'b00)) |-> (Y == 1'b0)
    );

    // A1 high forces Y high.
    check_y_forced_one_by_A1: assert property (
        @(posedge CLK) A1 |-> (Y == 1'b1)
    );

    // A2 high with A1 low forces Y high.
    check_y_forced_one_by_A2_when_A1_zero: assert property (
        @(posedge CLK) (A2 && !A1) |-> (Y == 1'b1)
    );

    // A3 high with A1,A2 low forces Y high.
    check_y_forced_one_by_A3_when_A1_A2_zero: assert property (
        @(posedge CLK) (A3 && !A2 && !A1) |-> (Y == 1'b1)
    );

    // If B==0 and Y==1, at least one A must be 1.
    check_y_one_with_b_zero_implies_some_A_one: assert property (
        @(posedge CLK) (Y && (B == 2'b00)) |-> (A1 || A2 || A3)
    );

endmodule