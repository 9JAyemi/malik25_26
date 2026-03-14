module ones_complement_sva (
    input logic clk,
    input logic [3:0] binary,
    input logic [3:0] ones_comp
);
    // Clock: clk (posedge). No reset in RTL.
    // Mixed logic: combinational double inversion feeding a registered output.
    // Behavior: ones_comp captures binary (one-cycle latency).

    // Output captures the previous cycle's input value.
    check_output_captures_prev_input: assert property (
        @(posedge clk) $past(1'b1) |-> (ones_comp == $past(binary))
    );

    // If input is stable over the last cycle, output equals current input.
    check_equal_when_input_stable: assert property (
        @(posedge clk) $past(1'b1) && $stable(binary) |-> (ones_comp == binary)
    );

    // If input changed over the last cycle, output differs from current input.
    check_inequal_when_input_changed: assert property (
        @(posedge clk) $past(1'b1) && !$stable(binary) |-> (ones_comp != binary)
    );

    // Any output change implies a change on the input in the prior cycle.
    check_output_change_implies_prior_input_change: assert property (
        @(posedge clk) $past(1'b1,2) && $changed(ones_comp) |-> $changed($past(binary))
    );

    // If input was constant for two consecutive prior cycles, output does not change.
    check_no_output_change_if_input_constant_two_cycles: assert property (
        @(posedge clk) $past(1'b1,2) && ($past(binary) == $past(binary,2)) |-> !$changed(ones_comp)
    );

    // A change on the input in the prior cycle causes an output change this cycle.
    check_prior_input_change_implies_output_change: assert property (
        @(posedge clk) $past(1'b1,2) && $changed($past(binary)) |-> $changed(ones_comp)
    );
endmodule