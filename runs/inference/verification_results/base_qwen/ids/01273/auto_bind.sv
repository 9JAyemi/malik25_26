// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): CLK, RESETn, cin_driven_by_lower_adder, assert, property, posedge, disable, iff, lower_adder_sum_correct, higher_adder_sum_correct, cin_zero_when_no_carry, cin_one_when_carry, b1, sum_within_valid_range, hFFFFFFFF, cin_zero_when_inputs_zero, cin_one_when_inputs_one, sum_zero_when_inputs_zero, sum_correct_when_inputs_one, h100000000
bind carry_lookahead_adder top_module_sva auto_sva_inst (
    .a(a),
    .b(b),
    .sum(sum),
    .a_low(a_low),
    .b_low(b_low),
    .a_high(a_high),
    .b_high(b_high),
    .cin(cin),
    .carry_lookahead_adder(carry_lookahead_adder),
    .adder_low(adder_low),
    .b0(b0),
    .cout(cout),
    .adder_high(adder_high)
);
