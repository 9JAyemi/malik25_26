module clock_divider_sva #(
    parameter int unsigned div_factor = 2
) (
    input  logic clk_in,
    input  logic rst,
    input  logic clk_out
);

    ///// Reset behavior /////
    // While reset is asserted, clk_out must be 0.
    reset_drives_low: assert property (
        @(posedge clk_in) rst |-> (clk_out == 1'b0)
    );

    // If reset is held high across cycles, clk_out stays at 0 and stable.
    reset_holds_low_stable: assert property (
        @(posedge clk_in) (rst && $past(rst)) |-> (clk_out == 1'b0) && $stable(clk_out)
    );

    ///// Active behavior /////
    // When active (not in reset), any change on clk_out is by inversion of its previous value.
    invert_on_toggle_when_active: assert property (
        @(posedge clk_in) disable iff (rst)
            ($changed(clk_out) && !$isunknown($past(clk_out)) && !$isunknown(clk_out)) |-> (clk_out == ~$past(clk_out))
    );

    // Properties that depend on div_factor being at least 1.
    generate
        if (div_factor >= 1) begin : gen_df_ge_1
            // After a toggle, there are exactly (div_factor-1) stable cycles, then a toggle.
            toggle_period_exact: assert property (
                @(posedge clk_in) disable iff (rst)
                    $changed(clk_out) |-> $stable(clk_out)[* (div_factor - 1)] ##1 $changed(clk_out)
            );

            // Starting at any cycle, if clk_out remains stable for (div_factor-1) cycles, it toggles next.
            must_toggle_after_wait: assert property (
                @(posedge clk_in) disable iff (rst)
                    $stable(clk_out)[* (div_factor - 1)] |-> ##1 $changed(clk_out)
            );

            // After reset de-asserts, the first toggle occurs after exactly div_factor cycles.
            first_toggle_after_reset: assert property (
                @(posedge clk_in) disable iff (rst)
                    $fell(rst) |-> $stable(clk_out)[* (div_factor - 1)] ##1 $changed(clk_out)
            );

            // For div_factor > 1, no back-to-back toggles in consecutive cycles.
            if (div_factor > 1) begin : gen_df_gt_1
                no_adjacent_toggles: assert property (
                    @(posedge clk_in) disable iff (rst)
                        $changed(clk_out) |-> ##1 !$changed(clk_out)
                );
            end
        end
    endgenerate

endmodule