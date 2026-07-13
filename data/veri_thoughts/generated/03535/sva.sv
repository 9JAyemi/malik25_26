module altera_tse_xcvr_resync_sva #(
    parameter integer SYNC_CHAIN_LENGTH = 2,
    parameter integer WIDTH             = 1,
    parameter integer SLOW_CLOCK        = 0
) (
    input logic             clk,
    input logic [WIDTH-1:0] d,
    input logic [WIDTH-1:0] q
);

    localparam integer INT_LEN = (SYNC_CHAIN_LENGTH > 0) ? SYNC_CHAIN_LENGTH : 1;

    genvar ig;
    generate
        for (ig = 0; ig < WIDTH; ig = ig + 1) begin : gen_bit_assertions

            // A sampled input rise must be visible at q after the resync latency.
            check_input_rise_reaches_output: assert property (
                @(posedge clk) disable iff (1'b0)
                $rose(d[ig]) |-> ##INT_LEN q[ig]
            );

            if (INT_LEN == 1) begin : gen_len1_common
                // If d is low while q is high, q clears on the next clk.
                check_output_clears_after_low_hold: assert property (
                    @(posedge clk) disable iff (1'b0)
                    (q[ig] && !d[ig]) |=> !q[ig]
                );
            end else begin : gen_lenN_common
                // If d stays low while q is high, q clears after the chain latency.
                check_output_clears_after_low_hold: assert property (
                    @(posedge clk) disable iff (1'b0)
                    ((q[ig] && !d[ig]) ##1 (!d[ig])[*INT_LEN-1]) |=> !q[ig]
                );
            end

            if (SLOW_CLOCK == 0) begin : gen_fast_clock_assertions

                // A sampled high on d must appear as high on q after INT_LEN clks.
                check_input_high_reaches_output: assert property (
                    @(posedge clk) disable iff (1'b0)
                    d[ig] |-> ##INT_LEN q[ig]
                );

                // A sampled low on d must appear as low on q after INT_LEN clks.
                check_input_low_reaches_output: assert property (
                    @(posedge clk) disable iff (1'b0)
                    !d[ig] |-> ##INT_LEN !q[ig]
                );

                // q matches d delayed by INT_LEN clk cycles once history exists.
                check_output_matches_delayed_input: assert property (
                    @(posedge clk) disable iff (1'b0)
                    (!$past($initstate, INT_LEN)) |-> (q[ig] == $past(d[ig], INT_LEN))
                );

                // An output rise must come from an input rise INT_LEN cycles earlier.
                check_output_rise_tracks_input_rise: assert property (
                    @(posedge clk) disable iff (1'b0)
                    ((!$past($initstate, INT_LEN+1)) && $rose(q[ig])) |-> $past($rose(d[ig]), INT_LEN)
                );

                // An output fall must come from an input fall INT_LEN cycles earlier.
                check_output_fall_tracks_input_fall: assert property (
                    @(posedge clk) disable iff (1'b0)
                    ((!$past($initstate, INT_LEN+1)) && $fell(q[ig])) |-> $past($fell(d[ig]), INT_LEN)
                );

            end
        end
    endgenerate

endmodule