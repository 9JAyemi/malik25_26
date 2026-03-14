module adder_sva (
    input logic CLK,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic C,
    input logic [7:0] sum
);
    // When C=0 the sum equals A+B (8-bit truncation).
    check_sum_when_C0: assert property (
        @(posedge CLK) (C == 1'b0) |-> (sum == (A + B))
    );

    // When C=1 the sum equals two's complement of (A+B).
    check_sum_when_C1: assert property (
        @(posedge CLK) (C == 1'b1) |-> (sum == (~(A + B) + 8'd1))
    );

    // Sum is zero whenever (A+B) is zero, regardless of C.
    check_zero_result_on_zero_input_sum: assert property (
        @(posedge CLK) ((A + B) == 8'h00) |-> (sum == 8'h00)
    );

    // Sum changes only if at least one input (A,B,C) changes.
    check_output_only_changes_on_input_change: assert property (
        @(posedge CLK) $changed(sum) |-> ($changed(A) || $changed(B) || $changed(C))
    );

    // If inputs are stable cycle-to-cycle, sum is stable.
    check_stable_output_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && $stable(C)) |-> $stable(sum)
    );

    // Rising C edge with stable A,B complements previous sum.
    check_c_rise_complements_sum: assert property (
        @(posedge CLK) ($rose(C) && $stable(A) && $stable(B)) |-> (sum == (~$past(sum) + 8'd1))
    );

    // Falling C edge with stable A,B complements previous sum.
    check_c_fall_complements_sum: assert property (
        @(posedge CLK) ($fell(C) && $stable(A) && $stable(B)) |-> (sum == (~$past(sum) + 8'd1))
    );

    // Sum is always within 8-bit range.
    check_sum_within_range: assert property (
        @(posedge CLK) (sum <= 8'hFF)
    );

    // For C=1, sum plus (A+B) wraps to zero (8-bit).
    check_twos_complement_sum_cancel: assert property (
        @(posedge CLK) (C == 1'b1) |-> (((sum + (A + B)) == 8'h00))
    );

    // For C=0, sum cancels with two's complement of (A+B) to zero.
    check_normal_sum_cancel_with_negated_ab: assert property (
        @(posedge CLK) (C == 1'b0) |-> (((sum + (~(A + B) + 8'd1)) == 8'h00))
    );
endmodule