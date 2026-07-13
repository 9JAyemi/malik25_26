module io1_sub_sva (
    input wire lower_ina,
    input wire sec_ina,
    input wire lower_io,
    input wire sec_io,
    input wire lower_out,
    input wire sec_out
);

    // lower_out is the OR of lower_ina and lower_io.
    check_lower_out_or: assert property (
        @($global_clock) lower_out === (lower_ina | lower_io)
    );

    // sec_out is the OR of sec_ina and sec_io.
    check_sec_out_or: assert property (
        @($global_clock) sec_out === (sec_ina | sec_io)
    );

    // lower_out must be high if either lower input is high.
    check_lower_out_high_when_any_input_high: assert property (
        @($global_clock) ((lower_ina === 1'b1) || (lower_io === 1'b1)) |-> (lower_out === 1'b1)
    );

    // sec_out must be high if either sec input is high.
    check_sec_out_high_when_any_input_high: assert property (
        @($global_clock) ((sec_ina === 1'b1) || (sec_io === 1'b1)) |-> (sec_out === 1'b1)
    );

    // lower_out must be low when both lower inputs are low.
    check_lower_out_low_when_both_inputs_low: assert property (
        @($global_clock) ((lower_ina === 1'b0) && (lower_io === 1'b0)) |-> (lower_out === 1'b0)
    );

    // sec_out must be low when both sec inputs are low.
    check_sec_out_low_when_both_inputs_low: assert property (
        @($global_clock) ((sec_ina === 1'b0) && (sec_io === 1'b0)) |-> (sec_out === 1'b0)
    );

    // lower_out stays stable when its inputs stay stable.
    check_lower_out_stable_when_inputs_stable: assert property (
        @($global_clock) ($stable(lower_ina) && $stable(lower_io)) |-> $stable(lower_out)
    );

    // sec_out stays stable when its inputs stay stable.
    check_sec_out_stable_when_inputs_stable: assert property (
        @($global_clock) ($stable(sec_ina) && $stable(sec_io)) |-> $stable(sec_out)
    );

endmodule