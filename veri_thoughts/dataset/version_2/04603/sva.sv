module mult_sva (
    input logic clock,
    input logic signed [15:0] x,
    input logic signed [15:0] y,
    input logic signed [30:0] product,
    input logic enable_in,
    input logic enable_out
);

    // When enabled, product captures the prior cycle's truncated multiply result.
    check_product_mult_when_enabled: assert property (
        @(posedge clock)
        enable_in |=> (product == (($past(x) * $past(y))[30:0]))
    );

    // When disabled, product is cleared on the next cycle.
    check_product_zero_when_disabled: assert property (
        @(posedge clock)
        !enable_in |=> (product == 31'sd0)
    );

    // enable_out is a one-cycle delayed copy of enable_in.
    check_enable_out_delay: assert property (
        @(posedge clock)
        1'b1 |=> (enable_out == $past(enable_in))
    );

endmodule