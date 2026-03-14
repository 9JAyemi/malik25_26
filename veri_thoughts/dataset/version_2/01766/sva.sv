module signal_combiner_sva (
    input logic [7:0] input_signals,
    input logic       output_signal
);
    // No clock or reset in DUT; pure combinational logic.
    // Assertions sample on any input bit edge to check combinational relationships.

    // Default clock: any edge on any input bit.
    default clocking comb_cb @(
        posedge input_signals[0] or negedge input_signals[0] or
        posedge input_signals[1] or negedge input_signals[1] or
        posedge input_signals[2] or negedge input_signals[2] or
        posedge input_signals[3] or negedge input_signals[3] or
        posedge input_signals[4] or negedge input_signals[4] or
        posedge input_signals[5] or negedge input_signals[5] or
        posedge input_signals[6] or negedge input_signals[6] or
        posedge input_signals[7] or negedge input_signals[7]
    ); endclocking

    // Local re-computation of DUT combinational logic from ports.
    wire [7:0] inv = ~input_signals;
    wire [7:0] num_ones_local;
    assign num_ones_local = {
        inv[0] & input_signals[1],
        inv[1] & input_signals[2],
        inv[2] & input_signals[3],
        inv[3] & input_signals[4],
        inv[4] & input_signals[5],
        inv[5] & input_signals[6],
        inv[6] & input_signals[7],
        inv[7]
    };
    wire [3:0] sum_all    = num_ones_local[0] + num_ones_local[1] + num_ones_local[2] + num_ones_local[3]
                           + num_ones_local[4] + num_ones_local[5] + num_ones_local[6] + num_ones_local[7];
    wire [3:0] sum_others =                  /* exclude num_ones_local[0] = ~input_signals[7] */
                              num_ones_local[1] + num_ones_local[2] + num_ones_local[3]
                            + num_ones_local[4] + num_ones_local[5] + num_ones_local[6] + num_ones_local[7];
    wire       computed_output = (sum_all >= 4);

    // Output equals the DUT's defined threshold function (sum_all >= 4).
    check_output_definition: assert property (output_signal == computed_output);

    // If fewer than 4 contributing terms, output must be 0.
    check_output_low_when_count_lt4: assert property ((sum_all < 4) |-> (output_signal == 1'b0));

    // If at least 4 contributing terms, output must be 1.
    check_output_high_when_count_ge4: assert property ((sum_all >= 4) |-> (output_signal == 1'b1));

    // All inputs 0 -> only ~input_signals[7] contributes; count=1 -> output 0.
    check_pattern_all_zeros: assert property ((input_signals == 8'h00) |-> (output_signal == 1'b0));

    // All inputs 1 -> no terms contribute; count=0 -> output 0.
    check_pattern_all_ones: assert property ((input_signals == 8'hFF) |-> (output_signal == 1'b0));

    // Alternating 0101_0101 yields exactly 4 contributing terms -> output 1.
    check_pattern_55: assert property ((input_signals == 8'h55) |-> (output_signal == 1'b1));

    // Alternating 1010_1010 yields exactly 4 contributing terms -> output 1.
    check_pattern_AA: assert property ((input_signals == 8'hAA) |-> (output_signal == 1'b1));

    // If MSB is 0 (so ~input_signals[7] contributes 1) and 3 other terms are 1 -> output 1.
    check_msb_zero_plus_three_pairs: assert property (((input_signals[7] == 1'b0) && (sum_others >= 3)) |-> (output_signal == 1'b1));

    // If MSB is 1 (so ~input_signals[7] contributes 0), require 4 other terms to assert -> output 1.
    check_msb_one_requires_four_pairs: assert property (((input_signals[7] == 1'b1) && (sum_others >= 4)) |-> (output_signal == 1'b1));

endmodule