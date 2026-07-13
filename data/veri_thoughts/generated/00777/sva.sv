module adder_subtractor_4bit_sva (
    input  logic CLK,
    input  logic [3:0] a,
    input  logic [3:0] b,
    input  logic       sub,
    input  logic [3:0] sum
);
    ///// Functional checks /////
    // When sub==0, sum equals a + b (mod 16).
    check_add_when_sub0: assert property (
        @(posedge CLK) (!sub) |-> (sum == (a + b))
    );

    // When sub==1, sum equals a - b (mod 16).
    check_sub_when_sub1: assert property (
        @(posedge CLK) (sub) |-> (sum == (a - b))
    );

    // Output remains stable if a, b, and sub are stable across a cycle.
    check_stable_output_when_inputs_stable: assert property (
        @(posedge CLK) $stable({a,b,sub}) |-> $stable(sum)
    );

    // Switching from add to sub with same inputs yields a - b.
    check_toggle_to_sub: assert property (
        @(posedge CLK) ($past(sub)==1'b0 && sub==1'b1 && $stable(a) && $stable(b)) |-> (sum == (a - b))
    );

    // Switching from sub to add with same inputs yields a + b.
    check_toggle_to_add: assert property (
        @(posedge CLK) ($past(sub)==1'b1 && sub==1'b0 && $stable(a) && $stable(b)) |-> (sum == (a + b))
    );

    // Addition identity: adding zero on b returns a.
    check_add_zero_b: assert property (
        @(posedge CLK) (!sub && (b == 4'd0)) |-> (sum == a)
    );

    // Subtraction identity: subtracting zero returns a.
    check_sub_zero_b: assert property (
        @(posedge CLK) (sub && (b == 4'd0)) |-> (sum == a)
    );

    // Subtraction of equal operands yields zero.
    check_sub_equal_operands_zero: assert property (
        @(posedge CLK) (sub && (a == b)) |-> (sum == 4'd0)
    );

    // No X/Z on output when all inputs are known 0/1.
    check_no_x_on_known_inputs: assert property (
        @(posedge CLK) !$isunknown({a,b,sub}) |-> !$isunknown(sum)
    );
endmodule