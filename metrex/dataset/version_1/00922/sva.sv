// SVA for decade_counter: bind-only, concise, and focused on key behaviors

module decade_counter_sva (
    input  logic       clk,
    input  logic       reset,
    input  logic       pause,
    input  logic [3:0] q,
    input  logic [3:0] johnson,
    input  logic       flip_flop
);

    // No X after reset is deasserted
    property p_no_x;
        @(posedge clk) !reset |-> !$isunknown({johnson, flip_flop, q});
    endproperty
    assert property (p_no_x);

    // Synchronous reset drives known values at the clock edge
    property p_reset_vals_now;
        @(posedge clk) reset |-> ##0 (johnson==4'b0001 && flip_flop==1'b0 && q==4'b0000);
    endproperty
    assert property (p_reset_vals_now);

    // Pause holds architected state
    property p_pause_holds_all;
        @(posedge clk) disable iff (reset)
        pause |=> ($stable(johnson) && $stable(flip_flop) && $stable(q));
    endproperty
    assert property (p_pause_holds_all);

    // Johnson register next-state function when not paused
    property p_johnson_next;
        @(posedge clk) disable iff (reset)
        (!pause) |=> johnson ==
                     { $past(johnson[2]) ^ $past(johnson[3]),
                       $past(johnson[1]),
                       $past(johnson[0]),
                       $past(johnson[3]) };
    endproperty
    assert property (p_johnson_next);

    // flip_flop control: toggle only when johnson==4'b1001, else hold (when not paused)
    property p_ff_toggle_on_1001;
        @(posedge clk) disable iff (reset)
        (!pause && (johnson==4'b1001)) |=> (flip_flop == ~$past(flip_flop));
    endproperty
    assert property (p_ff_toggle_on_1001);

    property p_ff_hold_else;
        @(posedge clk) disable iff (reset)
        (!pause && (johnson!=4'b1001)) |=> (flip_flop == $past(flip_flop));
    endproperty
    assert property (p_ff_hold_else);

    // q update mapping: uses current johnson and flip_flop sampled in the prior cycle
    property p_q_update;
        @(posedge clk) disable iff (reset)
        (!pause) |=> (q == ($past(flip_flop) ? 4'b0000 : $past(johnson)));
    endproperty
    assert property (p_q_update);

    // Coverage: reset release, pause activity, johnson update, flip_flop toggle opportunity
    cover property (@(posedge clk) reset ##1 !reset);
    cover property (@(posedge clk) disable iff (reset) pause ##1 !pause ##1 pause);
    cover property (@(posedge clk) disable iff (reset) (!pause) ##1 (q == $past(johnson)));
    cover property (@(posedge clk) disable iff (reset) (!pause && (johnson==4'b1001)) ##1 (flip_flop != $past(flip_flop)));

endmodule

bind decade_counter decade_counter_sva sva_dc (
    .clk(clk),
    .reset(reset),
    .pause(pause),
    .q(q),
    .johnson(johnson),
    .flip_flop(flip_flop)
);