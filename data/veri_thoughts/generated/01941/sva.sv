module binary_counter_sva (
    input logic clock,
    input logic [3:0] q
);
    // Clock: clock (posedge). No reset. Sequential 4-bit up-counter with wrap to 0 at 15.

    // When q is 15, next value must be 0.
    check_wrap_on_max: assert property (
        @(posedge clock) (q == 4'hF) |=> (q == 4'h0)
    );

    // When q is not 15, next value increments by 1.
    check_increment_when_not_max: assert property (
        @(posedge clock) (q != 4'hF) |=> (q == $past(q) + 4'd1)
    );

    // q must change every cycle (no stutter).
    check_no_stutter: assert property (
        @(posedge clock) 1'b1 |=> (q != $past(q))
    );

    // LSB toggles every cycle.
    check_lsb_toggles: assert property (
        @(posedge clock) 1'b1 |=> (q[0] != $past(q[0]))
    );

    // Bit1 updates with carry from bit0: next q[1] = past q[1] XOR past q[0].
    check_bit1_updates_with_carry: assert property (
        @(posedge clock) 1'b1 |=> (q[1] == ($past(q[1]) ^ $past(q[0])))
    );

    // Bit2 updates with carry from bits[1:0]: next q[2] = past q[2] XOR (past q[1] & past q[0]).
    check_bit2_updates_with_carry: assert property (
        @(posedge clock) 1'b1 |=> (q[2] == ($past(q[2]) ^ ($past(q[1]) & $past(q[0]))))
    );

    // Bit3 updates with carry from bits[2:0]: next q[3] = past q[3] XOR (past q[2] & past q[1] & past q[0]).
    check_bit3_updates_with_carry: assert property (
        @(posedge clock) 1'b1 |=> (q[3] == ($past(q[3]) ^ ($past(q[2]) & $past(q[1]) & $past(q[0]))))
    );

    // After 16 cycles, q returns to its prior value (period 16).
    check_periodicity_16: assert property (
        @(posedge clock) 1'b1 |-> ##16 (q == $past(q,16))
    );

    // If q is 0 now, it must have been 15 in the previous cycle.
    check_zero_preceded_by_max: assert property (
        @(posedge clock) 1'b1 |=> ((q == 4'h0) |-> ($past(q) == 4'hF))
    );

    // After 2 cycles, q advances by +2 modulo 16.
    check_two_cycle_step: assert property (
        @(posedge clock) 1'b1 |-> ##2 (q == (($past(q,2) + 4'd2) & 4'hF))
    );
endmodule