module digital_potentiometer_sva #(
    parameter n = 8
) (
    input logic [n-1:0] din,
    input logic         clk,
    input logic         en,
    input logic [n-1:0] dout,
    input logic [n-1:0] shift_reg,
    input logic [n-1:0] resistance
);

    function automatic logic [n-1:0] pot_value(input logic [n-1:0] code);
        pot_value = (code == '0) ? '0 : (1 << (code - 1));
    endfunction

    // Enabled cycles load din into shift_reg.
    check_shift_reg_captures_din: assert property (
        @(posedge clk) en |=> (shift_reg == $past(din))
    );

    // Disabled cycles hold shift_reg unchanged.
    check_shift_reg_holds_when_disabled: assert property (
        @(posedge clk) !en |=> (shift_reg == $past(shift_reg))
    );

    // resistance always matches the combinational decode of shift_reg.
    check_resistance_matches_decode: assert property (
        @(posedge clk) (resistance == pot_value(shift_reg))
    );

    // dout is always the current resistance value.
    check_dout_matches_resistance: assert property (
        @(posedge clk) (dout == resistance)
    );

    // An enabled capture updates dout from the sampled din on the next cycle.
    check_enable_updates_dout_from_din: assert property (
        @(posedge clk) en |=> (dout == pot_value($past(din)))
    );

    // A disabled cycle keeps dout unchanged on the next cycle.
    check_disable_holds_dout: assert property (
        @(posedge clk) !en |=> (dout == $past(dout))
    );

    // Capturing zero drives the output to zero on the next cycle.
    check_zero_capture_drives_zero: assert property (
        @(posedge clk) en && (din == '0) |=> (dout == '0)
    );

endmodule