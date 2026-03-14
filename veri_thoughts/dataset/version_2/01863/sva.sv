module xor_gate_sva (
    input logic a,
    input logic b,
    input logic out
);
    // No clk/reset in RTL; assertions clocked on $global_clock.

    // Output equals XOR of inputs at all times.
    check_truth_xor: assert property (
        @(posedge $global_clock) out == (a ^ b)
    );

    // Truth-table: 00 -> 0.
    check_tt_00_zero: assert property (
        @(posedge $global_clock) (a == 1'b0 && b == 1'b0) |-> (out == 1'b0)
    );

    // Truth-table: 01 -> 1.
    check_tt_01_one: assert property (
        @(posedge $global_clock) (a == 1'b0 && b == 1'b1) |-> (out == 1'b1)
    );

    // Truth-table: 10 -> 1.
    check_tt_10_one: assert property (
        @(posedge $global_clock) (a == 1'b1 && b == 1'b0) |-> (out == 1'b1)
    );

    // Truth-table: 11 -> 0.
    check_tt_11_zero: assert property (
        @(posedge $global_clock) (a == 1'b1 && b == 1'b1) |-> (out == 1'b0)
    );

    // If inputs are stable cycle-to-cycle, output is stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge $global_clock) (a == $past(a) && b == $past(b)) |-> (out == $past(out))
    );

    // If only a changes cycle-to-cycle, output toggles.
    check_toggle_on_a_only: assert property (
        @(posedge $global_clock) (a != $past(a) && b == $past(b)) |-> (out != $past(out))
    );

    // If only b changes cycle-to-cycle, output toggles.
    check_toggle_on_b_only: assert property (
        @(posedge $global_clock) (b != $past(b) && a == $past(a)) |-> (out != $past(out))
    );

    // If both inputs change cycle-to-cycle, output is unchanged.
    check_no_change_when_both_change: assert property (
        @(posedge $global_clock) (a != $past(a) && b != $past(b)) |-> (out == $past(out))
    );
endmodule