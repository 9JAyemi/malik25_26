module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] d,
    input logic a,
    input logic b,
    input logic c,
    input logic [7:0] q,
    input logic [3:0] mux_out,
    input logic [7:0] flip_flops_out
);

    // Mux output is always one-hot.
    check_mux_out_onehot: assert property (
        @(posedge clk) disable iff (reset)
        $onehot(mux_out)
    );

    // Mux output is always a subset of q.
    check_mux_subset_q: assert property (
        @(posedge clk) disable iff (reset)
        (mux_out & ~q) == 4'b0000
    );

    // Mux output is never zero.
    check_mux_nonzero: assert property (
        @(posedge clk) disable iff (reset)
        mux_out != 4'b0000
    );

    // Mux selects 0001 when a, b, c are 000.
    check_mux_decode_000: assert property (
        @(posedge clk) disable iff (reset)
        ({c, b, a} == 3'b000) |-> (mux_out == 4'b0001)
    );

    // Mux selects 0010 when a, b, c are 001.
    check_mux_decode_001: assert property (
        @(posedge clk) disable iff (reset)
        ({c, b, a} == 3'b001) |-> (mux_out == 4'b0010)
    );

    // Mux selects 0100 when a, b, c are 010.
    check_mux_decode_010: assert property (
        @(posedge clk) disable iff (reset)
        ({c, b, a} == 3'b010) |-> (mux_out == 4'b0100)
    );

    // Mux selects 1000 when a, b, c are 011.
    check_mux_decode_011: assert property (
        @(posedge clk) disable iff (reset)
        ({c, b, a} == 3'b011) |-> (mux_out == 4'b1000)
    );

    // Mux selects 0011 when a, b, c are 100.
    check_mux_decode_100: assert property (
        @(posedge clk) disable iff (reset)
        ({c, b, a} == 3'b100) |-> (mux_out == 4'b0011)
    );

    // Mux selects 0110 when a, b, c are 101.
    check_mux_decode_101: assert property (
        @(posedge clk) disable iff (reset)
        ({c, b, a} == 3'b101) |-> (mux_out == 4'b0110)
    );

    // Mux selects 1100 when a, b, c are 110.
    check_mux_decode_110: assert property (
        @(posedge clk) disable iff (reset)
        ({c, b, a} == 3'b110) |-> (mux_out == 4'b1100)
    );

    // Mux selects 1111 when a, b, c are 111.
    check_mux_decode_111: assert property (
        @(posedge clk) disable iff (reset)
        ({c, b, a} == 3'b111) |-> (mux_out == 4'b1111)
    );

    // Flip-flop output is zero whenever reset is asserted.
    check_ff_reset_clears_q: assert property (
        @(posedge clk)
        reset |-> (flip_flops_out == 8'b00000000)
    );

    // Flip-flop output is zero whenever the counter is 111.
    check_ff_counter_111_clears_q: assert property (
        @(posedge clk) disable iff (reset)
        (flip_flops_out == 8'b00000000) |-> (flip_flops_out == 8'b00000000)
    );

    // Flip-flop output is d on the next cycle when the counter is 111.
    check_ff_loads_d_on_111: assert property (
        @(posedge clk) disable iff (reset)
        (flip_flops_out == 8'b00000000) |-> (flip_flops_out == d)
    );

    // Flip-flop output holds its value when the counter is not 111.
    check_ff_holds_when_not_111: assert property (
        @(posedge clk) disable iff (reset)
        (flip_flops_out != 8'b00000000) |-> (flip_flops_out == $past(flip_flops_out))
    );

    // q is always a subset of flip-flop output.
    check_q_subset_ff_out: assert property (
        @(posedge clk) disable iff (reset)
        (q & ~flip_flops_out) == 8'b00000000
    );

    // q is always a subset of mux output.
    check_q_subset_mux_out: assert property (
        @(posedge clk) disable iff (reset)
        (q & ~mux_out) == 8'b00000000
    );

    // q is never zero.
    check_q_nonzero: assert property (
        @(posedge clk) disable iff (reset)
        q != 8'b00000000
    );

    // q is always one-hot.
    check_q_onehot: assert property (
        @(posedge clk) disable iff (reset)
        $onehot(q)
    );

endmodule