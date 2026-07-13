module binary_ones_counter_sva (
    input logic CLK,
    input logic [15:0] data_in,
    input logic [3:0] ones_count
);
    // 5-bit popcount of 16-bit vector
    function automatic [4:0] popcnt16_5 (input logic [15:0] v);
        automatic int k;
        automatic [4:0] c;
        begin
            c = 5'd0;
            for (k = 0; k < 16; k++) c = c + v[k];
            popcnt16_5 = c;
        end
    endfunction

    // One-hot detector for 16-bit vector
    function automatic bit is_onehot16 (input logic [15:0] v);
        is_onehot16 = (v != 16'b0) && ((v & (v - 16'd1)) == 16'b0);
    endfunction

    ///// Functional correctness /////
    // ones_count equals the number of 1s in data_in modulo 16.
    check_count_matches_mod16: assert property (
        @(posedge CLK) ones_count == popcnt16_5(data_in)[3:0]
    );

    // Zero input produces zero output.
    check_zero_input: assert property (
        @(posedge CLK) (data_in == 16'd0) |-> (ones_count == 4'd0)
    );

    // All ones input overflows to zero (16 mod 16 == 0).
    check_all_ones_input: assert property (
        @(posedge CLK) (data_in == 16'hFFFF) |-> (ones_count == 4'd0)
    );

    // Exactly one bit set yields ones_count == 1.
    check_onehot_input: assert property (
        @(posedge CLK) is_onehot16(data_in) |-> (ones_count == 4'd1)
    );

    ///// Temporal consistency /////
    // If data_in is stable, ones_count must be stable.
    check_hold_when_input_stable: assert property (
        @(posedge CLK) (data_in == $past(data_in)) |-> (ones_count == $past(ones_count))
    );

    // Single rising bit increases ones_count by 1 modulo 16.
    check_inc_on_single_rise: assert property (
        @(posedge CLK)
            is_onehot16(data_in ^ $past(data_in)) &&
            ((data_in & ~ $past(data_in)) != 16'b0)
        |-> (ones_count == ($past(ones_count) + 4'd1))
    );

    // Single falling bit decreases ones_count by 1 modulo 16.
    check_dec_on_single_fall: assert property (
        @(posedge CLK)
            is_onehot16(data_in ^ $past(data_in)) &&
            ((~data_in & $past(data_in)) != 16'b0)
        |-> (ones_count == ($past(ones_count) - 4'd1))
    );

    // Complementing all bits flips count to (16 - previous) modulo 16.
    check_complement_relation: assert property (
        @(posedge CLK) (data_in == ~ $past(data_in)) |-> (ones_count == (4'd0 - $past(ones_count)))
    );

    // Two rising bits increase ones_count by 2 modulo 16.
    check_inc2_on_double_rise: assert property (
        @(posedge CLK)
            (popcnt16_5(data_in & ~ $past(data_in)) == 5'd2) &&
            (popcnt16_5(~data_in & $past(data_in)) == 5'd0)
        |-> (ones_count == ($past(ones_count) + 4'd2))
    );

    // Two falling bits decrease ones_count by 2 modulo 16.
    check_dec2_on_double_fall: assert property (
        @(posedge CLK)
            (popcnt16_5(~data_in & $past(data_in)) == 5'd2) &&
            (popcnt16_5(data_in & ~ $past(data_in)) == 5'd0)
        |-> (ones_count == ($past(ones_count) - 4'd2))
    );

    // One rise and one fall (net zero) leaves ones_count unchanged.
    check_no_change_on_one_rise_one_fall: assert property (
        @(posedge CLK)
            (popcnt16_5(data_in & ~ $past(data_in)) == 5'd1) &&
            (popcnt16_5(~data_in & $past(data_in)) == 5'd1)
        |-> (ones_count == $past(ones_count))
    );
endmodule