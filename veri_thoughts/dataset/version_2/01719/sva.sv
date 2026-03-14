module calculator_sva (
    input logic        rst,
    input logic        clk,
    input logic [7:0]  a,
    input logic [7:0]  b,
    input logic [1:0]  op,
    input logic [7:0]  result,
    input logic        valid
);
    // While reset (active LOW), outputs are cleared.
    reset_outputs_cleared: assert property (
        @(posedge clk) (!rst) |-> (result == 8'h00) && (valid == 1'b0)
    );

    // valid cannot be HIGH when reset is asserted.
    valid_only_when_not_in_reset: assert property (
        @(posedge clk) valid |-> rst
    );

    // With valid HIGH, result matches previous-cycle addition (op==00).
    check_add_result: assert property (
        @(posedge clk) disable iff (!rst)
            (valid && ($past(op) == 2'b00)) |-> (result == ($past(a) + $past(b)))
    );

    // With valid HIGH, result matches previous-cycle subtraction (op==01).
    check_sub_result: assert property (
        @(posedge clk) disable iff (!rst)
            (valid && ($past(op) == 2'b01)) |-> (result == ($past(a) - $past(b)))
    );

    // With valid HIGH, result matches lower 8b of previous-cycle multiplication (op==10).
    check_mul_result: assert property (
        @(posedge clk) disable iff (!rst)
            (valid && ($past(op) == 2'b10)) |-> (result == (($past(a) * $past(b)) [7:0]))
    );

    // With valid HIGH, result matches previous-cycle division (op==11) when divisor != 0.
    check_div_result_nonzero: assert property (
        @(posedge clk) disable iff (!rst)
            (valid && ($past(op) == 2'b11) && ($past(b) != 8'h00)) |-> (result == ($past(a) / $past(b)))
    );

    // With valid HIGH and stable inputs/op (and no div-by-zero), result holds its previous value.
    stable_result_when_inputs_stable: assert property (
        @(posedge clk) disable iff (!rst)
            (valid && $stable(op) && $stable(a) && $stable(b) && ((op != 2'b11) || (b != 8'h00)))
            |-> (result == $past(result))
    );

    // With valid HIGH, multiply-by-zero yields zero.
    mul_by_zero_yields_zero: assert property (
        @(posedge clk) disable iff (!rst)
            (valid && ($past(op) == 2'b10) && (($past(a) == 8'h00) || ($past(b) == 8'h00)))
            |-> (result == 8'h00)
    );

    // With valid HIGH, add with b==0 returns a.
    add_with_b_zero_identity: assert property (
        @(posedge clk) disable iff (!rst)
            (valid && ($past(op) == 2'b00) && ($past(b) == 8'h00))
            |-> (result == $past(a))
    );

    // With valid HIGH, subtract with b==0 returns a.
    sub_with_b_zero_identity: assert property (
        @(posedge clk) disable iff (!rst)
            (valid && ($past(op) == 2'b01) && ($past(b) == 8'h00))
            |-> (result == $past(a))
    );

    // With valid HIGH, divide by one returns a.
    div_by_one_identity: assert property (
        @(posedge clk) disable iff (!rst)
            (valid && ($past(op) == 2'b11) && ($past(b) == 8'h01))
            |-> (result == $past(a))
    );

endmodule