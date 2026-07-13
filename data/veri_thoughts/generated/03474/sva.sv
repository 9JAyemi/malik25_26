module xor_gate_pipeline_sva (
    input logic       a,
    input logic       b,
    input logic       out_comb,
    input logic [1:0] stage1,
    input logic [1:0] stage2
);

    // No explicit clock or reset exists in the RTL; sample on the formal global clock.

    // stage1[0] captures the current XOR whenever an input changes.
    check_stage1_capture: assert property (
        @($global_clock)
        (!$initstate && ($changed(a) || $changed(b))) |-> (stage1[0] == (a ^ b))
    );

    // stage1[1] shifts in the previous stage1[0] value on an input change.
    check_stage1_shift: assert property (
        @($global_clock)
        (!$initstate && ($changed(a) || $changed(b))) |-> (stage1[1] == $past(stage1[0]))
    );

    // stage2[0] shifts in the previous stage1[1] value on an input change.
    check_stage2_shift0: assert property (
        @($global_clock)
        (!$initstate && ($changed(a) || $changed(b))) |-> (stage2[0] == $past(stage1[1]))
    );

    // stage2[1] shifts in the previous stage2[0] value on an input change.
    check_stage2_shift1: assert property (
        @($global_clock)
        (!$initstate && ($changed(a) || $changed(b))) |-> (stage2[1] == $past(stage2[0]))
    );

    // out_comb captures the previous stage2[1] value on an input change.
    check_output_shift: assert property (
        @($global_clock)
        (!$initstate && ($changed(a) || $changed(b))) |-> (out_comb == $past(stage2[1]))
    );

    // All pipeline state holds when neither input changes.
    check_state_holds_without_input_change: assert property (
        @($global_clock)
        (!$initstate && !$changed(a) && !$changed(b)) |-> ($stable(stage1) && $stable(stage2) && $stable(out_comb))
    );

    // out_comb can only change when an input changes.
    check_output_change_requires_input_change: assert property (
        @($global_clock)
        (!$initstate && $changed(out_comb)) |-> ($changed(a) || $changed(b))
    );

    // stage1 can only change when an input changes.
    check_stage1_change_requires_input_change: assert property (
        @($global_clock)
        (!$initstate && $changed(stage1)) |-> ($changed(a) || $changed(b))
    );

    // stage2 can only change when an input changes.
    check_stage2_change_requires_input_change: assert property (
        @($global_clock)
        (!$initstate && $changed(stage2)) |-> ($changed(a) || $changed(b))
    );

endmodule

bind xor_gate_pipeline xor_gate_pipeline_sva xor_gate_pipeline_sva_inst (
    .a(a),
    .b(b),
    .out_comb(out_comb),
    .stage1(stage1),
    .stage2(stage2)
);