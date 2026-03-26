module dff_64_sva (
    input logic        clk,
    input logic        rst,
    input logic [63:0] d,
    input logic [63:0] q
);

    // Sampled active-low reset keeps q cleared.
    check_reset_forces_zero: assert property (
        @(posedge clk) disable iff ($initstate)
            !rst |-> (q == 64'b0)
    );

    // The first clock after a sampled reset still sees q cleared.
    check_post_reset_zero: assert property (
        @(posedge clk) disable iff (!rst || $initstate)
            $past(!rst) |-> (q == 64'b0)
    );

    // A previously sampled zero input must produce a zero output.
    check_zero_data_captures_zero: assert property (
        @(posedge clk) disable iff (!rst || $initstate)
            ($past(rst) && ($past(d) == 64'b0)) |-> (q == 64'b0)
    );

    // Out of reset, q is either cleared by reset or equal to the prior d.
    check_q_is_zero_or_prior_d: assert property (
        @(posedge clk) disable iff (!rst || $initstate)
            ((q == 64'b0) || (q == $past(d)))
    );

    // Any nonzero q value must match the previously sampled d.
    check_nonzero_q_matches_prior_d: assert property (
        @(posedge clk) disable iff (!rst || $initstate)
            (q != 64'b0) |-> (q == $past(d))
    );

    // Any nonzero q value implies reset was high on the prior sample.
    check_nonzero_q_requires_prior_rst_high: assert property (
        @(posedge clk) disable iff (!rst || $initstate)
            (q != 64'b0) |-> $past(rst)
    );

endmodule