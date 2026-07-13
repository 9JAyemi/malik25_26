module xor_shift_register_sva (
    input logic clk,
    input logic load,
    input logic [1:0] ena,
    input logic [99:0] data,
    input logic [99:0] q,
    input logic out_if_else
);

    ///// Combinational output relationship /////
    // out_if_else reflects whether q and data differ on any bit.
    check_out_matches_neq: assert property (
        @(posedge clk) out_if_else == (q != data)
    );
    // out_if_else equals the reduction-OR of q ^ data.
    check_out_matches_xor_or: assert property (
        @(posedge clk) out_if_else == (|(q ^ data))
    );

    ///// Next-state behavior /////
    // Complete next-state function for q (priority: load over ena!=0).
    check_next_state_function: assert property (
        @(posedge clk) 1'b1 |=> q == (
            $past(load) ? $past(data) :
            (($past(ena) != 2'b00) ? {$past(q[97:0]), $past(q[99:98])} : $past(q))
        )
    );
    // When load is asserted, q loads data on the next cycle.
    check_load_updates_from_data: assert property (
        @(posedge clk) load |=> (q == $past(data))
    );
    // When load is deasserted and ena!=0, q rotates left by 2 bits.
    check_shift_when_ena_nonzero: assert property (
        @(posedge clk) (!load && (ena != 2'b00)) |=> (q == {$past(q[97:0]), $past(q[99:98])})
    );
    // When load is deasserted and ena==0, q holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) (!load && (ena == 2'b00)) |=> (q == $past(q))
    );
    // Upper bits shift down by 2 when rotating (bits [99:2] from prior [97:0]).
    check_shift_upper_bits: assert property (
        @(posedge clk) (!load && (ena != 2'b00)) |=> (q[99:2] == $past(q[97:0]))
    );
    // Lower bits wrap from prior top two bits when rotating (bits [1:0] from prior [99:98]).
    check_shift_lower_bits: assert property (
        @(posedge clk) (!load && (ena != 2'b00)) |=> (q[1:0] == $past(q[99:98]))
    );

    ///// Change qualification /////
    // q only changes across a cycle if previously load=1 or ena!=0.
    check_q_changes_only_when_allowed: assert property (
        @(posedge clk) (q != $past(q)) |-> ($past(load) || ($past(ena) != 2'b00))
    );

    ///// Output stability /////
    // If q and data are stable across a cycle, out_if_else is stable too.
    check_out_stable_if_inputs_stable: assert property (
        @(posedge clk) ($stable(q) && $stable(data)) |-> $stable(out_if_else)
    );

endmodule