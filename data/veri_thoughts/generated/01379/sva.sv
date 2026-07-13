module register_sva #(
    parameter WIDTH = 32
) (
    input logic clk,
    input logic en,
    input logic [WIDTH-1:0] din,
    input logic [WIDTH-1:0] dout
);
    // DUT: register; clock: clk (posedge); no reset; sequential posedge load when en=1.

    // At time 0, dout must be 0 due to initial data = 0.
    check_init_zero: assert property (
        @(posedge clk) $initstate |-> (dout == '0)
    );

    // When en is 1, dout updates on the next clock to the sampled din.
    check_update_on_en: assert property (
        @(posedge clk) (!$initstate && en) |=> (dout == $past(din))
    );

    // When en is 0, dout holds its previous value on the next clock.
    check_hold_when_en0: assert property (
        @(posedge clk) (!$initstate && !en) |=> (dout == $past(dout))
    );

    // Any change in dout between clocks implies en was 1 in the previous cycle.
    check_change_implies_past_en: assert property (
        @(posedge clk) (!$initstate && (dout != $past(dout))) |-> $past(en)
    );

    // If dout changes, it must equal the previous cycle's din.
    check_change_matches_past_din: assert property (
        @(posedge clk) (!$initstate && (dout != $past(dout))) |-> (dout == $past(din))
    );

    // Back-to-back enables: current dout must equal last cycle's din.
    check_back_to_back_en: assert property (
        @(posedge clk) (!$initstate && $past(en) && en) |-> (dout == $past(din))
    );

    // Idempotent write: if en=1 and din equals stored value, dout remains unchanged next cycle.
    check_idempotent_write: assert property (
        @(posedge clk) (!$initstate && en && (din == $past(dout))) |=> (dout == $past(dout))
    );

    // Two-cycle hold: if en=0 for two consecutive cycles, dout equals its value from two cycles ago.
    check_two_cycle_hold: assert property (
        @(posedge clk) (!$initstate && !$past($initstate) && !en && !$past(en)) |=> (dout == $past(dout,2))
    );

endmodule