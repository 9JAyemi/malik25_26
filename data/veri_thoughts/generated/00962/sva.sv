module updown_counter_sva (
    input logic clk,
    input logic U_D,
    input logic [3:0] Q
);
    ///// Counter update behavior /////
    // Q updates by +1 when U_D=1, else -1 (mod 16), on each clock after the first.
    check_update_rule: assert property (
        @(posedge clk) 1'b1 |=> (U_D ? (Q == $past(Q) + 4'd1) : (Q == $past(Q) - 4'd1))
    );

    // Q must change every cycle (never holds its value).
    check_q_always_changes: assert property (
        @(posedge clk) 1'b1 |=> $changed(Q)
    );

    // If counting up and previous Q was 15, wrap to 0.
    check_inc_wrap: assert property (
        @(posedge clk) 1'b1 |=> ( !(U_D && ($past(Q) == 4'hF)) || (Q == 4'h0) )
    );

    // If counting down and previous Q was 0, wrap to 15.
    check_dec_wrap: assert property (
        @(posedge clk) 1'b1 |=> ( !((!U_D) && ($past(Q) == 4'h0)) || (Q == 4'hF) )
    );

    // If counting up and previous Q != 15, increment by 1.
    check_inc_nonwrap: assert property (
        @(posedge clk) 1'b1 |=> ( !(U_D && ($past(Q) != 4'hF)) || (Q == $past(Q) + 4'd1) )
    );

    // If counting down and previous Q != 0, decrement by 1.
    check_dec_nonwrap: assert property (
        @(posedge clk) 1'b1 |=> ( !((!U_D) && ($past(Q) != 4'h0)) || (Q == $past(Q) - 4'd1) )
    );

    // The magnitude of the step each cycle is exactly 1 (mod 16).
    check_delta_one: assert property (
        @(posedge clk) 1'b1 |=> ( (Q == $past(Q) + 4'd1) || (Q == $past(Q) - 4'd1) )
    );

    // Exactly one of +1 or -1 delta holds each cycle.
    check_delta_exclusive: assert property (
        @(posedge clk) 1'b1 |=> ( (Q == $past(Q) + 4'd1) != (Q == $past(Q) - 4'd1) )
    );

    // U_D reflects the direction of change (increment iff U_D==1).
    check_direction_matches_delta: assert property (
        @(posedge clk) 1'b1 |=> ( U_D == (Q == $past(Q) + 4'd1) )
    );

    // LSB toggles every cycle due to +/-1 operation.
    check_lsb_toggle: assert property (
        @(posedge clk) 1'b1 |=> ( Q[0] != $past(Q[0]) )
    );
endmodule