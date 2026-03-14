module xor_counter_sva (
    input logic clk,
    input logic a,
    input logic out_comb_ff,
    input logic [1:0] out_counter,
    input logic [1:0] counter,
    input logic out_ff
);
    // Counter increments by 1 modulo-4 each clock.
    check_counter_increments: assert property (
        @(posedge clk) disable iff ($initstate) counter == $past(counter) + 2'b01
    );

    // out_counter captures the previous value of counter.
    check_out_counter_is_prev_counter: assert property (
        @(posedge clk) disable iff ($initstate) out_counter == $past(counter)
    );

    // In the same cycle, counter equals out_counter + 1.
    check_counter_equals_out_counter_plus1: assert property (
        @(posedge clk) counter == (out_counter + 2'b01)
    );

    // out_counter increments by 1 each clock (pipelined copy of counter).
    check_out_counter_increments: assert property (
        @(posedge clk) disable iff ($initstate) out_counter == $past(out_counter) + 2'b01
    );

    // out_ff captures the previous out_comb_ff.
    check_out_ff_captures_prev_out_comb_ff: assert property (
        @(posedge clk) disable iff ($initstate) out_ff == $past(out_comb_ff)
    );

    // out_comb_ff is always a XOR out_ff.
    check_out_comb_is_xor: assert property (
        @(posedge clk) out_comb_ff == (a ^ out_ff)
    );

    // out_ff equals previous (a XOR out_ff).
    check_out_ff_next_equals_prev_a_xor_out_ff: assert property (
        @(posedge clk) disable iff ($initstate) out_ff == $past(a ^ out_ff)
    );

    // If previous a was 1, out_ff toggles.
    check_out_ff_toggles_when_prev_a_1: assert property (
        @(posedge clk) disable iff ($initstate) $past(a) |-> (out_ff == ~$past(out_ff))
    );

    // If previous a was 0, out_ff holds.
    check_out_ff_holds_when_prev_a_0: assert property (
        @(posedge clk) disable iff ($initstate) !$past(a) |-> (out_ff == $past(out_ff))
    );

    // out_comb_ff equals a XOR previous out_comb_ff (via out_ff pipeline).
    check_out_comb_relates_to_prev_out_comb: assert property (
        @(posedge clk) disable iff ($initstate) out_comb_ff == (a ^ $past(out_comb_ff))
    );
endmodule