module counter_sva (
    input logic       clk,
    input logic       rst_n,
    input logic       en,
    input logic [3:0] out
);

    // Active-low reset forces the counter output to zero.
    reset_clears_out: assert property (
        @(posedge clk) !rst_n |-> (out == 4'b0000)
    );

    // The first sampled cycle after reset release still shows zero.
    release_from_reset_zero: assert property (
        @(posedge clk) disable iff (!rst_n || $initstate)
        $past(!rst_n) |-> (out == 4'b0000)
    );

    // When disabled, the counter holds unless async reset cleared it.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (!rst_n)
        !en |=> ((out == $past(out)) || (out == 4'b0000))
    );

    // When enabled, the counter increments unless async reset cleared it.
    increment_when_enabled: assert property (
        @(posedge clk) disable iff (!rst_n)
        en |=> ((out == ($past(out) + 4'd1)) || (out == 4'b0000))
    );

    // Enabling at 4'hF wraps the 4-bit counter to zero.
    wrap_from_max: assert property (
        @(posedge clk) disable iff (!rst_n)
        en && (out == 4'hF) |=> (out == 4'h0)
    );

endmodule