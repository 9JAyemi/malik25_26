module mux4to1_enable_sva (
    input logic [3:0] in,
    input logic en,
    input logic out
);

    // Out matches the implemented mux behavior.
    check_out_matches_implemented_mux: assert property (
        @($global_clock) out == (en ? in[0] : in[3])
    );

    // When enable is high, out selects in[0].
    check_enable_high_selects_in0: assert property (
        @($global_clock) en |-> (out == in[0])
    );

    // When enable is low, out selects in[3].
    check_enable_low_selects_in3: assert property (
        @($global_clock) !en |-> (out == in[3])
    );

    // A rising enable switches selection to in[0].
    check_enable_rise_selects_in0: assert property (
        @($global_clock) (!$initstate && $rose(en)) |-> (out == in[0])
    );

    // A falling enable switches selection to in[3].
    check_enable_fall_selects_in3: assert property (
        @($global_clock) (!$initstate && $fell(en)) |-> (out == in[3])
    );

    // Changing in[1] alone does not affect out.
    check_in1_is_unused: assert property (
        @($global_clock)
        (!$initstate && $stable(en) && $stable(in[0]) && $changed(in[1]) && $stable(in[2]) && $stable(in[3]))
        |-> $stable(out)
    );

    // Changing in[2] alone does not affect out.
    check_in2_is_unused: assert property (
        @($global_clock)
        (!$initstate && $stable(en) && $stable(in[0]) && $stable(in[1]) && $changed(in[2]) && $stable(in[3]))
        |-> $stable(out)
    );

    // With enable high, changing in[3] alone does not affect out.
    check_in3_unused_when_enabled: assert property (
        @($global_clock)
        (!$initstate && en && $stable(en) && $stable(in[0]) && $stable(in[1]) && $stable(in[2]) && $changed(in[3]))
        |-> $stable(out)
    );

    // With enable low, changing in[0] alone does not affect out.
    check_in0_unused_when_disabled: assert property (
        @($global_clock)
        (!$initstate && !en && $stable(en) && $changed(in[0]) && $stable(in[1]) && $stable(in[2]) && $stable(in[3]))
        |-> $stable(out)
    );

endmodule