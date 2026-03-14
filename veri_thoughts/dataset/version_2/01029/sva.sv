module shift_and_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic out
);
    // b low forces out low in the same cycle.
    check_b_zero_forces_out_zero: assert property (
        @(posedge clk) (b == 1'b0) |-> (out == 1'b0)
    );

    // out high implies b is high (AND gate behavior).
    check_out_one_implies_b_one: assert property (
        @(posedge clk) out |-> b
    );

    // After 3 cycles, out equals b AND the value of a from 3 cycles ago.
    check_out_matches_b_and_past_a_after_3: assert property (
        @(posedge clk) 1'b1 |-> ##3 (out == (b & $past(a,3)))
    );

    // If a is 1 now, out equals b after 3 cycles.
    check_a1_causes_out_eq_b_after_3: assert property (
        @(posedge clk) a |-> ##3 (out == b)
    );

    // If a is 0 now, out is 0 after 3 cycles.
    check_a0_causes_out0_after_3: assert property (
        @(posedge clk) !a |-> ##3 (out == 1'b0)
    );

    // When b is 1 after 3 cycles, out equals the value of a from 3 cycles ago.
    check_b1_selects_past_a_after_3: assert property (
        @(posedge clk) 1'b1 |-> ##3 (b |-> (out == $past(a,3)))
    );

    // If b falls in this cycle, out must be 0 in this cycle (combinational AND).
    check_fall_b_forces_out0_same_cycle: assert property (
        @(posedge clk) $fell(b) |-> (out == 1'b0)
    );

    // If b and the contributing a (3 cycles earlier) are both stable, out is stable.
    check_out_stable_when_inputs_stable: assert property (
        @(posedge clk) 1'b1 |-> ##4 ( ($stable(b) && ($past(a,3) == $past(a,4))) |-> $stable(out) )
    );
endmodule