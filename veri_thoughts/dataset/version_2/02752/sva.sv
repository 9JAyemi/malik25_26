module four_input_gate_sva (
    input logic CLK,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);
    // Y matches the RTL equation ~(A1 & A2) | ~(B1 & B2).
    check_functional_equation: assert property (
        @(posedge CLK) disable iff (1'b0) Y == ((~(A1 & A2)) | (~(B1 & B2)))
    );

    // When all inputs are 1, Y must be 0.
    check_all_ones_y_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (A1 & A2 & B1 & B2) |-> (Y == 1'b0)
    );

    // Y can be 0 only when all inputs are 1.
    check_y_zero_only_on_all_ones: assert property (
        @(posedge CLK) disable iff (1'b0) (Y == 1'b0) |-> (A1 & A2 & B1 & B2)
    );

    // If A1 is 0, Y must be 1.
    check_A1_zero_y_one: assert property (
        @(posedge CLK) disable iff (1'b0) (A1 == 1'b0) |-> (Y == 1'b1)
    );

    // If A2 is 0, Y must be 1.
    check_A2_zero_y_one: assert property (
        @(posedge CLK) disable iff (1'b0) (A2 == 1'b0) |-> (Y == 1'b1)
    );

    // If B1 is 0, Y must be 1.
    check_B1_zero_y_one: assert property (
        @(posedge CLK) disable iff (1'b0) (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // If B2 is 0, Y must be 1.
    check_B2_zero_y_one: assert property (
        @(posedge CLK) disable iff (1'b0) (B2 == 1'b0) |-> (Y == 1'b1)
    );

    // If A-group is not both 1, Y must be 1.
    check_A_group_zero_y_one: assert property (
        @(posedge CLK) disable iff (1'b0) (~(A1 & A2)) |-> (Y == 1'b1)
    );

    // If B-group is not both 1, Y must be 1.
    check_B_group_zero_y_one: assert property (
        @(posedge CLK) disable iff (1'b0) (~(B1 & B2)) |-> (Y == 1'b1)
    );

    // If not all inputs are 1, Y must be 1.
    check_not_all_ones_y_one: assert property (
        @(posedge CLK) disable iff (1'b0) !(A1 & A2 & B1 & B2) |-> (Y == 1'b1)
    );
endmodule