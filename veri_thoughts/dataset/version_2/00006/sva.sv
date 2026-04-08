module xor_adder_sva (
    input logic       clk,
    input logic [1:0] a,
    input logic [1:0] b,
    input logic [1:0] sum,
    input logic [1:0] stage1_sum,
    input logic [1:0] stage2_sum
);

property p_stage1_captures_input_xor;
    logic [1:0] exp_stage1;
    @(posedge clk)
        (exp_stage1 = (a ^ b), 1'b1)
        |=> (stage1_sum == exp_stage1);
endproperty

// stage1_sum loads a ^ b on the next clock.
check_stage1_captures_input_xor: assert property (p_stage1_captures_input_xor);

property p_stage2_captures_stage1_xor_sum;
    logic [1:0] exp_stage2;
    @(posedge clk)
        (exp_stage2 = (stage1_sum ^ sum), 1'b1)
        |=> (stage2_sum == exp_stage2);
endproperty

// stage2_sum loads stage1_sum ^ sum on the next clock.
check_stage2_captures_stage1_xor_sum: assert property (p_stage2_captures_stage1_xor_sum);

property p_sum_captures_stage2;
    logic [1:0] exp_sum;
    @(posedge clk)
        (exp_sum = stage2_sum, 1'b1)
        |=> (sum == exp_sum);
endproperty

// sum loads stage2_sum on the next clock.
check_sum_captures_stage2: assert property (p_sum_captures_stage2);

property p_stage2_matches_delayed_inputs_and_sum;
    logic [1:0] xor_ab;
    logic [1:0] exp_stage2;
    @(posedge clk)
        (xor_ab = (a ^ b), 1'b1) ##1
        (exp_stage2 = (xor_ab ^ sum), 1'b1)
        |=> (stage2_sum == exp_stage2);
endproperty

// stage2_sum matches the earlier input XOR combined with the prior sum.
check_stage2_matches_delayed_inputs_and_sum: assert property (p_stage2_matches_delayed_inputs_and_sum);

property p_sum_matches_stage1_and_sum_two_cycles_later;
    logic [1:0] exp_sum;
    @(posedge clk)
        (exp_sum = (stage1_sum ^ sum), 1'b1) ##1
        1'b1
        |=> (sum == exp_sum);
endproperty

// sum two clocks later equals the captured stage1_sum ^ sum value.
check_sum_matches_stage1_and_sum_two_cycles_later: assert property (p_sum_matches_stage1_and_sum_two_cycles_later);

property p_sum_matches_delayed_inputs_and_sum;
    logic [1:0] xor_ab;
    logic [1:0] exp_sum;
    @(posedge clk)
        (xor_ab = (a ^ b), 1'b1) ##1
        (exp_sum = (xor_ab ^ sum), 1'b1) ##1
        1'b1
        |=> (sum == exp_sum);
endproperty

// sum three clocks later matches the earlier input XOR and next-cycle sum.
check_sum_matches_delayed_inputs_and_sum: assert property (p_sum_matches_delayed_inputs_and_sum);

endmodule