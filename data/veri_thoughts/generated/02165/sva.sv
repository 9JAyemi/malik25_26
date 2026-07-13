module adder_4_2_sva (
    input logic [3:0] A,
    input logic [1:0] Y
);
    // No clock/reset in RTL; combinational; assertions sample on $global_clock.
    // Behavior: sum3=(A+2)[2:0]; Y = (sum3 > 3) ? 2'b11 : sum3[1:0].

    // Helper recomputation of RTL behavior
    logic [3:0] add4;
    logic [2:0] sum3;
    logic [1:0] expectedY;
    assign add4     = A + 4'd2;          // 4-bit add, as in RTL
    assign sum3     = add4[2:0];         // truncate to 3 bits, as in RTL
    assign expectedY= (sum3 > 3'd3) ? 2'b11 : sum3[1:0];

    // Y matches the recomputed RTL function
    check_y_functional_equivalence: assert property (
        @(posedge $global_clock) Y == expectedY
    );

    // When sum3 <= 3, Y passes through sum3[1:0]
    check_pass_through_when_sum_le3: assert property (
        @(posedge $global_clock) (sum3 <= 3'd3) |-> (Y == sum3[1:0])
    );

    // When sum3 > 3, Y saturates to 2'b11
    check_saturate_when_sum_gt3: assert property (
        @(posedge $global_clock) (sum3 > 3'd3) |-> (Y == 2'b11)
    );

    // If add4[2]==0 (sum3 in 0..3), Y equals add4[1:0]
    check_bit2_zero_pass_through: assert property (
        @(posedge $global_clock) (add4[2] == 1'b0) |-> (Y == add4[1:0])
    );

    // If add4[2]==1 (sum3 in 4..7), Y saturates to 2'b11
    check_bit2_one_saturate: assert property (
        @(posedge $global_clock) (add4[2] == 1'b1) |-> (Y == 2'b11)
    );

    // If input A is stable, output Y is stable (purely combinational)
    check_stable_input_implies_stable_output: assert property (
        @(posedge $global_clock) $stable(A) |-> $stable(Y)
    );

    // Function is periodic in A with period 8: f(A) == f(A+8)
    check_periodicity_plus8: assert property (
        @(posedge $global_clock) (A == ($past(A) + 4'd8)) |-> (Y == $past(Y))
    );

    // If Y == 0, the only possible sum3 is 0
    map_y_zero_implies_sum_zero: assert property (
        @(posedge $global_clock) (Y == 2'b00) |-> (sum3 == 3'd0)
    );

    // If Y == 1, the only possible sum3 is 1
    map_y_one_implies_sum_one: assert property (
        @(posedge $global_clock) (Y == 2'b01) |-> (sum3 == 3'd1)
    );

    // If Y == 2, the only possible sum3 is 2
    map_y_two_implies_sum_two: assert property (
        @(posedge $global_clock) (Y == 2'b10) |-> (sum3 == 3'd2)
    );

    // If Y == 3, sum3 must be >= 3
    map_y_three_implies_sum_ge3: assert property (
        @(posedge $global_clock) (Y == 2'b11) |-> (sum3 >= 3'd3)
    );

endmodule