module top_module_sva (
    input logic        clk,
    input logic [7:0]  a,
    input logic [7:0]  b,
    input logic [7:0]  s,
    input logic        overflow
);

    // No clock or reset exists in the RTL; clk only samples this combinational DUT.

    function automatic logic [7:0] neg8_fn(input logic [7:0] x);
        begin
            neg8_fn = ~x + 8'h01;
        end
    endfunction

    function automatic logic [7:0] adder_sum_fn(input logic [7:0] x, input logic [7:0] y);
        logic [8:0] add_res;
        logic [8:0] sub_res;
        begin
            add_res = {1'b0, x} + {1'b0, y};
            sub_res = {1'b0, x} + {1'b0, ~y} + 9'h001;
            adder_sum_fn = add_res[8] ? sub_res[7:0] : add_res[7:0];
        end
    endfunction

    function automatic logic adder_carry_fn(input logic [7:0] x, input logic [7:0] y);
        logic [8:0] add_res;
        begin
            add_res = {1'b0, x} + {1'b0, y};
            adder_carry_fn = add_res[8] ^ (x[7] ^ y[7]);
        end
    endfunction

    function automatic logic [7:0] top_sum_fn(input logic [7:0] x, input logic [7:0] y);
        logic [7:0] y_neg;
        begin
            y_neg = neg8_fn(y);
            top_sum_fn = adder_carry_fn(x, y) ? adder_sum_fn(x, y_neg) : adder_sum_fn(x, y);
        end
    endfunction

    function automatic logic top_overflow_fn(input logic [7:0] x, input logic [7:0] y);
        logic [7:0] y_neg;
        begin
            y_neg = neg8_fn(y);
            top_overflow_fn = adder_carry_fn(x, y) ^ adder_carry_fn(x, y_neg);
        end
    endfunction

    // s must match the top-level select between the two adder outputs.
    check_sum_matches_top_logic: assert property (
        @(posedge clk) s == top_sum_fn(a, b)
    );

    // overflow must match the XOR of the two internal adder carry_out values.
    check_overflow_matches_top_logic: assert property (
        @(posedge clk) overflow == top_overflow_fn(a, b)
    );

    // When the first adder carry_out is low, top selects the first adder sum.
    check_select_sum1_when_first_carry_low: assert property (
        @(posedge clk) !adder_carry_fn(a, b) |-> s == adder_sum_fn(a, b)
    );

    // When the first adder carry_out is high, top selects the second adder sum.
    check_select_sum2_when_first_carry_high: assert property (
        @(posedge clk) adder_carry_fn(a, b) |-> s == adder_sum_fn(a, neg8_fn(b))
    );

    // Matching internal carry_out values force overflow low.
    check_overflow_low_when_carries_match: assert property (
        @(posedge clk) (adder_carry_fn(a, b) == adder_carry_fn(a, neg8_fn(b))) |-> !overflow
    );

    // Different internal carry_out values force overflow high.
    check_overflow_high_when_carries_differ: assert property (
        @(posedge clk) (adder_carry_fn(a, b) != adder_carry_fn(a, neg8_fn(b))) |-> overflow
    );

    // With b equal to zero, the design passes a through and does not overflow.
    check_zero_b_passthrough: assert property (
        @(posedge clk) (b == 8'h00) |-> (s == a && overflow == 1'b0)
    );

    // 8'h80 is self-negating, so both adder instances produce the same carry_out.
    check_self_negating_b_has_no_overflow: assert property (
        @(posedge clk) (b == 8'h80) |-> (s == adder_sum_fn(a, 8'h80) && overflow == 1'b0)
    );

    // Stable sampled inputs must keep the sampled outputs stable.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> ($stable(s) && $stable(overflow))
    );

endmodule