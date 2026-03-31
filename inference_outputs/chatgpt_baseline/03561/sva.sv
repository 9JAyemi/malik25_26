module freq_divider_sva #(
    parameter int n = 2
) (
    input logic clk_in,
    input logic clk_out
);

    generate
        if (n > 0) begin : gen_freq_divider_checks
            // A rising clk_out stays high for n input clocks, then falls.
            check_clk_out_rise_period: assert property (
                @(posedge clk_in) $rose(clk_out) |=> (clk_out)[*(n-1)] ##1 $fell(clk_out)
            );

            // A falling clk_out stays low for n input clocks, then rises.
            check_clk_out_fall_period: assert property (
                @(posedge clk_in) $fell(clk_out) |=> (!clk_out)[*(n-1)] ##1 $rose(clk_out)
            );

            // clk_out cannot toggle again before n input clocks have elapsed.
            check_clk_out_no_early_retoggle: assert property (
                @(posedge clk_in) $changed(clk_out) |=> (!$changed(clk_out))[* (n-1)]
            );

            // clk_out toggles again exactly n input clocks after any toggle.
            check_clk_out_retoggle_after_n_cycles: assert property (
                @(posedge clk_in) $changed(clk_out) |-> ##n $changed(clk_out)
            );
        end
    endgenerate

endmodule