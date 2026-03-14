module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] N,
    input logic [3:0] B,
    input logic mode,
    input logic select,
    input logic [3:0] q
);
    ///// counter: reset and step rules /////
    // After a cycle with reset HIGH, counter must be 0 on the next clock.
    check_counter_reset_next_zero: assert property (
        @(posedge clk) disable iff (reset)
            $past(reset) |-> (counter_inst.count_out == 4'd0)
    );

    // If previous cycle was not in reset and count_out != N, it increments by 1.
    check_counter_increment: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(counter_inst.count_out) != $past(N))) |-> 
                (counter_inst.count_out == ($past(counter_inst.count_out) + 4'd1))
    );

    // If previous cycle was not in reset and count_out == N, it wraps to 0.
    check_counter_wrap_to_zero_on_match: assert property (
        @(posedge clk) disable iff (reset)
            (!$past(reset) && ($past(counter_inst.count_out) == $past(N))) |-> 
                (counter_inst.count_out == 4'd0)
    );

    ///// adder_subtractor: combinational function /////
    // In add mode, out equals A + B (A is counter_inst.count_out).
    check_adder_add_mode: assert property (
        @(posedge clk) disable iff (reset)
            mode |-> (adder_subtractor_inst.out == (counter_inst.count_out + B))
    );

    // In sub mode, out equals A - B (A is counter_inst.count_out).
    check_adder_sub_mode: assert property (
        @(posedge clk) disable iff (reset)
            !mode |-> (adder_subtractor_inst.out == (counter_inst.count_out - B))
    );

    ///// q register: loads selected source on each clock /////
    // If previous cycle selected counter path, q equals previous count_out.
    check_q_load_prev_count_on_select1: assert property (
        @(posedge clk) disable iff (reset)
            $past(select) |-> (q == $past(counter_inst.count_out))
    );

    // If previous cycle selected adder/subtractor path, q equals previous out.
    check_q_load_prev_out_on_select0: assert property (
        @(posedge clk) disable iff (reset)
            !$past(select) |-> (q == $past(adder_subtractor_inst.out))
    );

    ///// End-to-end: when select stays HIGH, q behaves like the counter /////
    // With select HIGH in consecutive cycles, q steps by +1 unless it hits N, then wraps to 0.
    check_q_steps_like_counter_when_select_held: assert property (
        @(posedge clk) disable iff (reset)
            ($past(select) && select && !$past(reset)) |-> 
                (q == (($past(q) == $past(N)) ? 4'd0 : ($past(q) + 4'd1)))
    );

    // With select HIGH in consecutive cycles and q hit N previously, q must be 0 now.
    check_q_wrap_when_select_held: assert property (
        @(posedge clk) disable iff (reset)
            ($past(select) && select && !$past(reset) && ($past(q) == $past(N))) |-> 
                (q == 4'd0)
    );

    // With select HIGH in consecutive cycles and q != N previously, q increments by 1.
    check_q_inc_when_select_held_not_at_N: assert property (
        @(posedge clk) disable iff (reset)
            ($past(select) && select && !$past(reset) && ($past(q) != $past(N))) |-> 
                (q == ($past(q) + 4'd1))
    );
endmodule