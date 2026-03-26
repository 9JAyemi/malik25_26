module top_module_sva (
    input logic       clk,
    input logic       reset,
    input logic [7:0] d,
    input logic [7:0] q,
    input logic [7:0] in,
    input logic [2:0] pos
);

    // Reset forces q low.
    check_q_zero_during_reset: assert property (
        @(posedge clk) reset |-> (q == 8'b0)
    );

    // pos must match the priority encoder for in.
    check_pos_priority_encoding: assert property (
        @(posedge clk) disable iff (reset)
        pos == (in[7] ? 3'b111 :
                in[6] ? 3'b110 :
                in[5] ? 3'b101 :
                in[4] ? 3'b100 :
                in[3] ? 3'b011 :
                in[2] ? 3'b010 :
                in[1] ? 3'b001 :
                        3'b000)
    );

    // A default case selection drives q to zero on the following cycle.
    check_q_default_case_zero: assert property (
        @(posedge clk) disable iff (reset)
        ($past(!reset) &&
         ($past(pos) != 3'b000) &&
         ($past(pos) != 3'b001)) |-> (q == 8'b0)
    );

    // After a normal register-path selection, q reflects d from two cycles earlier.
    check_q_register_path_after_active_cycle: assert property (
        @(posedge clk) disable iff (reset)
        ($past(!reset) &&
         $past(!reset, 2) &&
         ($past(pos) == 3'b000)) |-> (q == $past(d, 2))
    );

    // On the first active cycle after reset, a register-path selection still outputs zero.
    check_q_register_path_first_cycle_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        ($past(!reset) &&
         $past(reset, 2) &&
         ($past(pos) == 3'b000)) |-> (q == 8'b0)
    );

    // On the first active cycle after reset, a counter-path selection outputs zero.
    check_q_counter_path_first_cycle_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        ($past(!reset) &&
         $past(reset, 2) &&
         ($past(pos) == 3'b001)) |-> (q == 8'b0)
    );

    // Back-to-back counter-path selections make q increment by one.
    check_q_counter_path_consecutive_increment: assert property (
        @(posedge clk) disable iff (reset)
        ($past(!reset) &&
         $past(!reset, 2) &&
         ($past(pos) == 3'b001) &&
         ($past(pos, 2) == 3'b001)) |-> (q == ($past(q) + 8'h01))
    );

endmodule