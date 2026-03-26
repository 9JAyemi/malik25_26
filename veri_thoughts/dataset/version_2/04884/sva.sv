module oh_dsync_sva #(
    parameter int PS = 2,
    parameter int DELAY = 0
) (
    input logic clk,
    input logic nreset,
    input logic din,
    input logic dout
);

`ifndef CFG_ASIC
    localparam int TAP = DELAY[0] ? (PS + 1) : PS;

    // Reset drives the output low.
    check_reset_clears_output: assert property (
        @(posedge clk) !nreset |-> (dout == 1'b0)
    );

    // After reset release, the output stays low until the selected tap can fill.
    check_release_holds_output_low: assert property (
        @(posedge clk) disable iff (!nreset)
        $rose(nreset) |-> (dout == 1'b0)[*TAP]
    );

    // A sustained low input propagates to the output after the selected delay.
    check_low_level_propagates: assert property (
        @(posedge clk) disable iff (!nreset)
        ((din == 1'b0)[*TAP]) |=> (dout == 1'b0)
    );

    // A sustained high input propagates to the output after the selected delay.
    check_high_level_propagates: assert property (
        @(posedge clk) disable iff (!nreset)
        ((din == 1'b1)[*TAP]) |=> (dout == 1'b1)
    );

    generate
        if (TAP == 1) begin : gen_tap_eq_1
            // A rising input reaches a high output one clock later.
            check_rise_propagates_tap1: assert property (
                @(posedge clk) disable iff (!nreset)
                $rose(din) |=> (dout == 1'b1)
            );

            // A falling input reaches a low output one clock later.
            check_fall_propagates_tap1: assert property (
                @(posedge clk) disable iff (!nreset)
                $fell(din) |=> (dout == 1'b0)
            );
        end else begin : gen_tap_gt_1
            // A rising input held high long enough propagates to the output.
            check_rise_propagates_tapn: assert property (
                @(posedge clk) disable iff (!nreset)
                ($rose(din) ##1 (din == 1'b1)[*(TAP-1)]) |=> (dout == 1'b1)
            );

            // A falling input held low long enough propagates to the output.
            check_fall_propagates_tapn: assert property (
                @(posedge clk) disable iff (!nreset)
                ($fell(din) ##1 (din == 1'b0)[*(TAP-1)]) |=> (dout == 1'b0)
            );
        end
    endgenerate
`endif

endmodule