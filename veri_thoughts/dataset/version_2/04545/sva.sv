module twos_complement_sva (
    input logic clk,
    input logic rst_n,
    input logic en,
    input logic [3:0] in,
    input logic [3:0] out
);

    // While reset is asserted, the output is cleared.
    check_reset_clears_out: assert property (
        @(posedge clk) !rst_n |-> (out == 4'b0000)
    );

    // An enabled cycle updates out to the two's complement of the prior input.
    check_update_on_enable: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(en)) |-> (out == ((~$past(in)) + 4'b0001))
    );

    // A disabled cycle holds the previous output value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && !$past(en)) |-> (out == $past(out))
    );

    // Two's complement of zero remains zero when enabled.
    check_zero_maps_to_zero: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(en) && ($past(in) == 4'b0000)) |-> (out == 4'b0000)
    );

    // The 4-bit most-negative value is self-inverse when enabled.
    check_most_negative_self_inverse: assert property (
        @(posedge clk) disable iff (!rst_n)
        ($past(rst_n) && $past(en) && ($past(in) == 4'b1000)) |-> (out == 4'b1000)
    );

endmodule