module add_sub_4bit_sva (
    input  logic        CLK,     // external assertion clock (DUT has no clock/reset)
    input  logic [3:0]  num1,
    input  logic [3:0]  num2,
    input  logic        sub,
    input  logic [3:0]  result
);
    // Result matches selected operation each cycle.
    check_function_select: assert property (
        @(posedge CLK) result == (sub ? (num1 - num2) : (num1 + num2))
    );

    // When sub==0, result equals num1 + num2.
    check_add_path: assert property (
        @(posedge CLK) (sub == 1'b0) |-> (result == (num1 + num2))
    );

    // When sub==1, result equals num1 - num2.
    check_sub_path: assert property (
        @(posedge CLK) (sub == 1'b1) |-> (result == (num1 - num2))
    );

    // If inputs are stable, result is stable (pure combinational behavior).
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(num1) && $stable(num2) && $stable(sub)) |-> $stable(result)
    );

    // Addition identity: adding zero returns num1.
    check_add_zero_identity: assert property (
        @(posedge CLK) (sub == 1'b0 && (num2 == 4'b0000)) |-> (result == num1)
    );

    // Subtraction identity: subtracting zero returns num1.
    check_sub_zero_identity: assert property (
        @(posedge CLK) (sub == 1'b1 && (num2 == 4'b0000)) |-> (result == num1)
    );

    // Subtracting equal operands yields zero.
    check_sub_equal_operands_zero: assert property (
        @(posedge CLK) (sub == 1'b1 && (num1 == num2)) |-> (result == 4'b0000)
    );

    // Rising sub selects subtraction, with previous cycle showing addition if inputs unchanged.
    check_sub_rise_selects_diff: assert property (
        @(posedge CLK) ($rose(sub) && $stable(num1) && $stable(num2))
            |-> (result == (num1 - num2)) && ($past(result) == ($past(num1) + $past(num2)))
    );

    // Falling sub selects addition, with previous cycle showing subtraction if inputs unchanged.
    check_sub_fall_selects_sum: assert property (
        @(posedge CLK) ($fell(sub) && $stable(num1) && $stable(num2))
            |-> (result == (num1 + num2)) && ($past(result) == ($past(num1) - $past(num2)))
    );
endmodule