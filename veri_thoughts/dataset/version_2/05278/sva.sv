module shift_reg_comb_sva (
    input logic clk,
    input logic d,
    input logic [3:0] in,
    input logic out_and,
    input logic out_or,
    input logic out_xor,
    input logic [7:0] sum
);

    // out_and matches the two-level AND-OR function.
    check_out_and_function: assert property (
        @(posedge clk)
        out_and == ((in[0] & in[1]) | (in[2] & in[3]))
    );

    // out_or matches the two-level OR-AND function.
    check_out_or_function: assert property (
        @(posedge clk)
        out_or == ((in[0] | in[1]) & (in[2] | in[3]))
    );

    // out_xor matches the two-level XOR-AND function.
    check_out_xor_function: assert property (
        @(posedge clk)
        out_xor == ((in[0] ^ in[1]) & (in[2] ^ in[3]))
    );

    // The sum never uses bits above bit 3.
    check_sum_upper_bits_zero: assert property (
        @(posedge clk)
        sum[7:4] == 4'b0000
    );

    // After one clock, sum bit 0 reflects the first shift stage plus out_xor.
    check_sum_bit0_tracks_shift_stage0: assert property (
        @(posedge clk)
        (!$initstate) |-> (sum[0] == ($past(d,1) ^ out_xor))
    );

    // After two clocks, sum bit 1 reflects the second shift stage and bit-0 carry.
    check_sum_bit1_tracks_shift_stage1_and_carry: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate,1)) |->
            (sum[1] == ($past(d,2) ^ out_or ^ ($past(d,1) & out_xor)))
    );

    // After three clocks, sum equals delayed d history plus the combinational outputs.
    check_sum_matches_shifted_d_and_comb_logic: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate,1) && !$past($initstate,2)) |->
            (sum == ({5'b0, $past(d,3), $past(d,2), $past(d,1)} +
                     {5'b0, out_and, out_or, out_xor}))
    );

    // With zero combinational contribution, sum is only the shifted d history.
    check_sum_equals_shift_value_when_comb_zero: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate,1) && !$past($initstate,2) &&
         (out_and == 1'b0) && (out_or == 1'b0) && (out_xor == 1'b0)) |->
            (sum == {5'b0, $past(d,3), $past(d,2), $past(d,1)})
    );

    // With three zero d samples, sum is only the combinational contribution.
    check_sum_equals_comb_value_when_shift_history_zero: assert property (
        @(posedge clk)
        (!$initstate && !$past($initstate,1) && !$past($initstate,2) &&
         ($past(d,1) == 1'b0) && ($past(d,2) == 1'b0) && ($past(d,3) == 1'b0)) |->
            (sum == {5'b0, out_and, out_or, out_xor})
    );

endmodule