module compare_4_sva (
    input logic        ram_empty_fb_i_reg,
    input logic [4:0]  v1_reg,
    input logic        rd_en,
    input logic        out,
    input logic        comp1
);

    // Output matches the implemented combinational equation.
    check_output_equation: assert property (
        @($global_clock)
        ram_empty_fb_i_reg == !((|v1_reg[3:0]) & rd_en & out & comp1)
    );

    // A zero low nibble forces the output HIGH.
    check_zero_low_nibble_forces_high: assert property (
        @($global_clock)
        (v1_reg[3:0] == 4'b0000) |-> ram_empty_fb_i_reg
    );

    // Any LOW control input forces the output HIGH.
    check_low_control_forces_high: assert property (
        @($global_clock)
        (!rd_en || !out || !comp1) |-> ram_empty_fb_i_reg
    );

    // All controls HIGH with a nonzero low nibble force the output LOW.
    check_all_inputs_active_force_low: assert property (
        @($global_clock)
        (rd_en && out && comp1 && (v1_reg[3:0] != 4'b0000)) |-> !ram_empty_fb_i_reg
    );

    // A LOW output can only occur with all controls HIGH and a nonzero low nibble.
    check_low_output_has_required_conditions: assert property (
        @($global_clock)
        !ram_empty_fb_i_reg |-> (rd_en && out && comp1 && (v1_reg[3:0] != 4'b0000))
    );

    // Changing only v1_reg[4] does not affect the output.
    check_bit4_is_unused: assert property (
        @($global_clock)
        $changed(v1_reg[4]) &&
        $stable(v1_reg[3:0]) &&
        $stable(rd_en) &&
        $stable(out) &&
        $stable(comp1)
        |-> $stable(ram_empty_fb_i_reg)
    );

endmodule