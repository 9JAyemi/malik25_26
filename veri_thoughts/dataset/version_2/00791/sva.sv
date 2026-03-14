module xor_pipeline_sva (
    input logic CLK,
    input logic a,
    input logic b,
    input logic out
);
    ///// Functional equivalence /////
    // Output equals XOR of inputs each cycle.
    check_xor_function: assert property (
        @(posedge CLK) disable iff ($initstate) (out == (a ^ b))
    );

    ///// Stability properties /////
    // If inputs are stable across a cycle, output is stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff ($initstate) ($stable(a) && $stable(b)) |-> $stable(out)
    );

    ///// Toggle relationships /////
    // If only 'a' flips between cycles, output flips.
    check_out_toggles_when_only_a_flips: assert property (
        @(posedge CLK) disable iff ($initstate) ((a != $past(a)) && (b == $past(b))) |-> (out != $past(out))
    );
    // If only 'b' flips between cycles, output flips.
    check_out_toggles_when_only_b_flips: assert property (
        @(posedge CLK) disable iff ($initstate) ((b != $past(b)) && (a == $past(a))) |-> (out != $past(out))
    );
    // If both 'a' and 'b' flip (odd parity) between cycles, output holds.
    check_out_stable_when_both_flip: assert property (
        @(posedge CLK) disable iff ($initstate) ((a != $past(a)) && (b != $past(b))) |-> $stable(out)
    );
    // Output toggle parity equals XOR of input toggle parities.
    check_toggle_parity_matches_inputs: assert property (
        @(posedge CLK) disable iff ($initstate) ((out != $past(out)) == ((a != $past(a)) ^ (b != $past(b))))
    );

    ///// Useful XOR special cases /////
    // When b is 0, out follows a.
    check_b_zero_out_eq_a: assert property (
        @(posedge CLK) disable iff ($initstate) (b == 1'b0) |-> (out == a)
    );
    // When a is 0, out follows b.
    check_a_zero_out_eq_b: assert property (
        @(posedge CLK) disable iff ($initstate) (a == 1'b0) |-> (out == b)
    );
endmodule