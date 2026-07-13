module bin2gray_sva (
    input logic        clk,
    input logic [3:0]  bin,
    input logic [3:0]  gray,
    input logic [3:0]  prev_bin
);
    // Clock: clk (posedge). No reset in RTL. Sequential logic gated by bin !== prev_bin.

    // When bin differs from prev_bin, gray must be current-cycle bin encoded to Gray.
    check_gray_update_value: assert property (
        @(posedge clk) (bin !== prev_bin) |-> (gray === {bin[3], (bin[3]^bin[2]), (bin[2]^bin[1]), (bin[1]^bin[0])})
    );

    // Bit mapping MSB on update: gray[3] equals bin[3].
    check_gray_msb_mapping_on_update: assert property (
        @(posedge clk) (bin !== prev_bin) |-> (gray[3] === bin[3])
    );

    // Bit mapping bit2 on update: gray[2] equals bin[3]^bin[2].
    check_gray_bit2_mapping_on_update: assert property (
        @(posedge clk) (bin !== prev_bin) |-> (gray[2] === (bin[3]^bin[2]))
    );

    // Bit mapping bit1 on update: gray[1] equals bin[2]^bin[1].
    check_gray_bit1_mapping_on_update: assert property (
        @(posedge clk) (bin !== prev_bin) |-> (gray[1] === (bin[2]^bin[1]))
    );

    // Bit mapping bit0 on update: gray[0] equals bin[1]^bin[0].
    check_gray_bit0_mapping_on_update: assert property (
        @(posedge clk) (bin !== prev_bin) |-> (gray[0] === (bin[1]^bin[0]))
    );

    // After an update, prev_bin captures the prior-cycle bin.
    check_prev_bin_updates_next_cycle: assert property (
        @(posedge clk) (bin !== prev_bin) |=> (prev_bin === $past(bin))
    );

    // Any change on gray must coincide with update condition in that cycle.
    check_gray_change_requires_update_condition: assert property (
        @(posedge clk) $changed(gray) |-> (bin !== prev_bin)
    );

    // Any change on prev_bin must have been caused by update condition in the prior cycle.
    check_prev_bin_change_requires_prior_update: assert property (
        @(posedge clk) $changed(prev_bin) |-> $past(bin !== $past(prev_bin))
    );

    // If no update condition, hold gray and prev_bin stable into next cycle.
    check_hold_stable_when_equal: assert property (
        @(posedge clk) (bin === prev_bin) |=> (gray === $past(gray)) && (prev_bin === $past(prev_bin))
    );

    // If no update condition, gray equals Gray(bin) in that cycle.
    check_gray_function_when_equal: assert property (
        @(posedge clk) (bin === prev_bin) |-> (gray === {bin[3], (bin[3]^bin[2]), (bin[2]^bin[1]), (bin[1]^bin[0])})
    );

endmodule