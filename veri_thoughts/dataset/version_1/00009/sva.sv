module shift_reg_sva (
    input logic [7:0] dout,
    input logic       din,
    input logic       clk,
    input logic       en
);

    // An enabled cycle shifts prior bits toward the MSB and loads din into bit 0.
    check_shift_on_enable: assert property (
        @(posedge clk) $past(en) |-> dout == { $past(dout[6:0]), $past(din) }
    );

    // On an enabled cycle, bits [7:1] come from the prior bits [6:0].
    check_upper_bits_shift: assert property (
        @(posedge clk) $past(en) |-> dout[7:1] == $past(dout[6:0])
    );

    // On an enabled cycle, bit 0 captures the prior din value.
    check_lsb_loads_din: assert property (
        @(posedge clk) $past(en) |-> dout[0] == $past(din)
    );

    // A disabled cycle leaves the register contents unchanged.
    check_hold_when_disabled: assert property (
        @(posedge clk) !$past(en) |-> dout == $past(dout)
    );

    // Any observed output change must come from enable being high on the prior cycle.
    check_change_requires_enable: assert property (
        @(posedge clk) (dout != $past(dout)) |-> $past(en)
    );

endmodule