module not_gate_sva (
    input logic in,
    input logic out
);

    // Output must match the RTL continuous-assignment function.
    check_out_matches_rtl_function: assert property (
        @($global_clock) out === ~(in & in)
    );

    // A low input must drive the output high.
    check_low_input_drives_high_output: assert property (
        @($global_clock) (in == 1'b0) |-> (out === 1'b1)
    );

    // A high input must drive the output low.
    check_high_input_drives_low_output: assert property (
        @($global_clock) (in == 1'b1) |-> (out === 1'b0)
    );

endmodule