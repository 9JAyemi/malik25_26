module my_mac_sva (
    input logic clk,
    input logic reset,
    input logic ce,
    input logic [31:0] din0,
    input logic [31:0] din1,
    input logic [31:0] dout
);

    // Reset clears dout on the next clock.
    check_reset_clears_dout: assert property (
        @(posedge clk) reset |=> (dout == 32'h00000000)
    );

    // With ce low, dout holds its value.
    check_hold_when_ce_low: assert property (
        @(posedge clk) disable iff (reset) (!ce) |=> (dout == $past(dout))
    );

    // With ce high, dout updates with the previous din0*din1.
    check_update_when_ce_high: assert property (
        @(posedge clk) disable iff (reset) ce |=> (dout == ($past(dout) + ($past(din0) * $past(din1))))
    );

endmodule