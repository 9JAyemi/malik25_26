module v89d234_sva (
    input logic v41eb95,
    input logic [7:0] v39f831,
    input logic vf892a0,
    input logic [7:0] vb1c024
);

    // The output follows the enabled-register next-state function.
    check_enabled_register_transition: assert property (
        @(posedge v41eb95) disable iff (1'b0)
        1'b1 |=> vb1c024 == ($past(vf892a0) ? $past(v39f831) : $past(vb1c024))
    );

    // A high load captures the input value on the next cycle.
    check_capture_on_load: assert property (
        @(posedge v41eb95) disable iff (1'b0)
        vf892a0 |=> vb1c024 == $past(v39f831)
    );

    // A low load holds the previous output value.
    check_hold_without_load: assert property (
        @(posedge v41eb95) disable iff (1'b0)
        !vf892a0 |=> vb1c024 == $past(vb1c024)
    );

    // Loading a different value changes the output on the next cycle.
    check_load_new_value_changes_output: assert property (
        @(posedge v41eb95) disable iff (1'b0)
        vf892a0 && (v39f831 != vb1c024) |=> (vb1c024 == $past(v39f831)) && (vb1c024 != $past(vb1c024))
    );

    // Loading the same value leaves the output unchanged.
    check_load_same_value_keeps_output: assert property (
        @(posedge v41eb95) disable iff (1'b0)
        vf892a0 && (v39f831 == vb1c024) |=> vb1c024 == $past(vb1c024)
    );

endmodule