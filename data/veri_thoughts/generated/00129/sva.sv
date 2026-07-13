module add2_and_round_reg_sva
  #(parameter WIDTH=16)
  (
    input logic clk,
    input logic [WIDTH-1:0] in1,
    input logic [WIDTH-1:0] in2,
    input logic [WIDTH-1:0] sum
  );

    // Without carry-out, the registered sum is the truncated addition.
    check_no_carry_rounding: assert property (
        @(posedge clk)
        !$initstate &&
        (({1'b0, $past(in1)} + {1'b0, $past(in2)}) < {1'b1, {WIDTH{1'b0}}})
        |-> (sum == ($past(in1) + $past(in2)))
    );

    // With carry-out, the registered sum adds the carry back in.
    check_carry_rounding: assert property (
        @(posedge clk)
        !$initstate &&
        (({1'b0, $past(in1)} + {1'b0, $past(in2)}) >= {1'b1, {WIDTH{1'b0}}})
        |-> (sum == ($past(in1) + $past(in2) + 1'b1))
    );

    // Two zero inputs produce a zero output on the next clock.
    check_zero_inputs: assert property (
        @(posedge clk)
        !$initstate &&
        ($past(in1) == {WIDTH{1'b0}}) &&
        ($past(in2) == {WIDTH{1'b0}})
        |-> (sum == {WIDTH{1'b0}})
    );

    // A zero output can only come from two zero inputs.
    check_zero_output_only_from_zero_inputs: assert property (
        @(posedge clk)
        !$initstate &&
        (sum == {WIDTH{1'b0}})
        |-> (($past(in1) == {WIDTH{1'b0}}) &&
             ($past(in2) == {WIDTH{1'b0}}))
    );

    // A zero in1 passes in2 through to the registered output.
    check_in1_zero_passthrough: assert property (
        @(posedge clk)
        !$initstate &&
        ($past(in1) == {WIDTH{1'b0}})
        |-> (sum == $past(in2))
    );

    // A zero in2 passes in1 through to the registered output.
    check_in2_zero_passthrough: assert property (
        @(posedge clk)
        !$initstate &&
        ($past(in2) == {WIDTH{1'b0}})
        |-> (sum == $past(in1))
    );

    // All-ones plus one returns one after the end-around carry.
    check_all_ones_plus_one_returns_one: assert property (
        @(posedge clk)
        !$initstate &&
        ((($past(in1) == {WIDTH{1'b1}}) && ($past(in2) == 1'b1)) ||
         (($past(in2) == {WIDTH{1'b1}}) && ($past(in1) == 1'b1)))
        |-> (sum == 1'b1)
    );

    // All-ones plus all-ones returns all-ones after rounding.
    check_all_ones_plus_all_ones: assert property (
        @(posedge clk)
        !$initstate &&
        ($past(in1) == {WIDTH{1'b1}}) &&
        ($past(in2) == {WIDTH{1'b1}})
        |-> (sum == {WIDTH{1'b1}})
    );

endmodule