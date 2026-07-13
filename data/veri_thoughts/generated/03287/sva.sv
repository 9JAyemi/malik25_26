module top_module_sva (
    input logic [255:0] in,
    input logic [7:0] sel,
    input logic [49:0] in_maj,
    input logic out
);

    // out equals the selected input bit OR the numeric compare result.
    check_out_matches_selected_bit_or_threshold: assert property (
        @($global_clock) out == (in[sel] | (in_maj > 50'd25))
    );

    // Any in_maj value above 25 forces out high.
    check_in_maj_above_25_forces_out_high: assert property (
        @($global_clock) (in_maj > 50'd25) |-> (out == 1'b1)
    );

    // When the compare is false, out follows the selected input bit.
    check_in_maj_not_above_25_tracks_selected_bit: assert property (
        @($global_clock) !(in_maj > 50'd25) |-> (out == in[sel])
    );

    // A high selected input bit forces out high.
    check_selected_bit_high_forces_out_high: assert property (
        @($global_clock) (in[sel] == 1'b1) |-> (out == 1'b1)
    );

    // A low out requires both the selected bit and compare result to be low.
    check_out_low_requires_selected_bit_low_and_threshold_clear: assert property (
        @($global_clock) (out == 1'b0) |-> ((in[sel] == 1'b0) && !(in_maj > 50'd25))
    );

    // At an in_maj value of 25, out still follows the selected bit.
    check_boundary_25_tracks_selected_bit: assert property (
        @($global_clock) (in_maj == 50'd25) |-> (out == in[sel])
    );

    // At an in_maj value of 26, out is forced high.
    check_boundary_26_forces_out_high: assert property (
        @($global_clock) (in_maj == 50'd26) |-> (out == 1'b1)
    );

    // With sel at 0 and the compare false, out uses in[0].
    check_sel_0_uses_in_0_when_threshold_clear: assert property (
        @($global_clock) ((sel == 8'd0) && !(in_maj > 50'd25)) |-> (out == in[0])
    );

    // With sel at 255 and the compare false, out uses in[255].
    check_sel_255_uses_in_255_when_threshold_clear: assert property (
        @($global_clock) ((sel == 8'hFF) && !(in_maj > 50'd25)) |-> (out == in[255])
    );

endmodule