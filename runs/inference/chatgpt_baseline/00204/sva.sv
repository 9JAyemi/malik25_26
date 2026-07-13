module debounce_sva (
    input logic       clk,
    input logic       pb,
    input logic       pb_debounced,
    input logic [3:0] shift_reg
);

    // The shift register shifts prior samples and captures pb each clock.
    check_shift_reg_update: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> (shift_reg == {$past(shift_reg[2:0]), $past(pb)})
    );

    // The output is low when all four stored samples are zero.
    check_output_low_decode: assert property (
        @(posedge clk) disable iff (1'b0)
        (shift_reg == 4'b0000) |-> (pb_debounced == 1'b0)
    );

    // The output is high when any stored sample is one.
    check_output_high_decode: assert property (
        @(posedge clk) disable iff (1'b0)
        (shift_reg != 4'b0000) |-> (pb_debounced == 1'b1)
    );

    // Four consecutive low input samples clear the debounced output next cycle.
    check_four_lows_clear_output: assert property (
        @(posedge clk) disable iff (1'b0)
        (!pb)[*4] |=> (pb_debounced == 1'b0)
    );

    // One high input sample keeps the debounced output high for four cycles.
    check_high_sample_holds_output: assert property (
        @(posedge clk) disable iff (1'b0)
        pb |=> (pb_debounced == 1'b1)[*4]
    );

    // A low debounced output stays low if the next sampled input is also low.
    check_low_output_holds_with_low_input: assert property (
        @(posedge clk) disable iff (1'b0)
        (pb_debounced == 1'b0 && pb == 1'b0) |=> (pb_debounced == 1'b0)
    );

    // A low debounced output goes high after a sampled high input.
    check_low_output_rises_on_high_input: assert property (
        @(posedge clk) disable iff (1'b0)
        (pb_debounced == 1'b0 && pb == 1'b1) |=> (pb_debounced == 1'b1)
    );

endmodule