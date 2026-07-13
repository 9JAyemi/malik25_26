module bitwise_operators_sva #(
    parameter int n = 8
)(
    input logic CLK,
    input logic [n-1:0] num1,
    input logic [n-1:0] num2,
    input logic [n-1:0] result
);
    ///// Functional behavior /////
    // result must equal bitwise NOT of num1.
    check_result_is_not_of_num1: assert property (
        @(posedge CLK) result == ~num1
    );

    // result and num1 must have no overlapping 1s.
    check_result_and_num1_is_zero: assert property (
        @(posedge CLK) (result & num1) == {n{1'b0}}
    );

    // result or num1 must be all 1s.
    check_result_or_num1_is_ones: assert property (
        @(posedge CLK) (result | num1) == {n{1'b1}}
    );

    ///// Stability and independence /////
    // If only num2 changes while num1 is stable, result must remain stable.
    check_num2_independence_when_num1_stable: assert property (
        @(posedge CLK) disable iff ($initstate)
        $stable(num1) && !$stable(num2) |-> $stable(result)
    );

    // If both inputs are stable, result must be stable (pure combinational behavior).
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) disable iff ($initstate)
        $stable(num1) && $stable(num2) |-> $stable(result)
    );

    // Result bit toggles match num1 bit toggles across cycles.
    check_toggle_correlation_with_num1: assert property (
        @(posedge CLK) disable iff ($initstate)
        (result ^ $past(result)) == (num1 ^ $past(num1))
    );
endmodule