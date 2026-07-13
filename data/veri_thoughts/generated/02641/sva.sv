module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [99:0] in,
    input logic out_and,
    input logic out_or,
    input logic out_xor,
    input logic [3:0] Q,
    input logic [3:0] out_sum
);
    // AND gate output equals in[0] & in[1].
    check_out_and_function: assert property (
        @(posedge clk) disable iff (reset) out_and == (in[0] & in[1])
    );
    // OR gate output equals in[0] | in[1].
    check_out_or_function: assert property (
        @(posedge clk) disable iff (reset) out_or == (in[0] | in[1])
    );
    // XOR gate output equals in[0] ^ in[1].
    check_out_xor_function: assert property (
        @(posedge clk) disable iff (reset) out_xor == (in[0] ^ in[1])
    );

    // On reset, Johnson counter output is 4'b0000 (synchronous, active-high).
    check_reset_drives_Q_zero: assert property (
        @(posedge clk) reset |-> (Q == 4'b0000)
    );

    // Johnson counter next-state from 0000 -> 0001.
    check_johnson_next_from_0000: assert property (
        @(posedge clk) disable iff (reset) (Q == 4'b0000) |=> (Q == 4'b0001)
    );
    // Johnson counter next-state from 0001 -> 0011.
    check_johnson_next_from_0001: assert property (
        @(posedge clk) disable iff (reset) (Q == 4'b0001) |=> (Q == 4'b0011)
    );
    // Johnson counter next-state from 0011 -> 0111.
    check_johnson_next_from_0011: assert property (
        @(posedge clk) disable iff (reset) (Q == 4'b0011) |=> (Q == 4'b0111)
    );
    // Johnson counter next-state from 0111 -> 1111.
    check_johnson_next_from_0111: assert property (
        @(posedge clk) disable iff (reset) (Q == 4'b0111) |=> (Q == 4'b1111)
    );
    // Johnson counter next-state from 1111 -> 1110.
    check_johnson_next_from_1111: assert property (
        @(posedge clk) disable iff (reset) (Q == 4'b1111) |=> (Q == 4'b1110)
    );
    // Johnson counter next-state from 1110 -> 1100.
    check_johnson_next_from_1110: assert property (
        @(posedge clk) disable iff (reset) (Q == 4'b1110) |=> (Q == 4'b1100)
    );
    // Johnson counter next-state from 1100 -> 1000.
    check_johnson_next_from_1100: assert property (
        @(posedge clk) disable iff (reset) (Q == 4'b1100) |=> (Q == 4'b1000)
    );
    // Johnson counter next-state from 1000 -> 0000.
    check_johnson_next_from_1000: assert property (
        @(posedge clk) disable iff (reset) (Q == 4'b1000) |=> (Q == 4'b0000)
    );

    // out_sum mapping when Q == 0001.
    check_out_sum_when_Q_0001: assert property (
        @(posedge clk) disable iff (reset) (Q == 4'b0001) |-> (out_sum == (out_xor + 4'b0001))
    );
    // out_sum mapping when Q == 0011.
    check_out_sum_when_Q_0011: assert property (
        @(posedge clk) disable iff (reset) (Q == 4'b0011) |-> (out_sum == (out_xor + 4'b0011))
    );
    // out_sum mapping when Q == 0111.
    check_out_sum_when_Q_0111: assert property (
        @(posedge clk) disable iff (reset) (Q == 4'b0111) |-> (out_sum == (out_xor + 4'b0111))
    );
    // out_sum mapping when Q == 1111.
    check_out_sum_when_Q_1111: assert property (
        @(posedge clk) disable iff (reset) (Q == 4'b1111) |-> (out_sum == (out_xor + 4'b1111))
    );
    // out_sum mapping when Q == 1110.
    check_out_sum_when_Q_1110: assert property (
        @(posedge clk) disable iff (reset) (Q == 4'b1110) |-> (out_sum == (out_xor + 4'b1110))
    );
    // out_sum mapping when Q == 1100.
    check_out_sum_when_Q_1100: assert property (
        @(posedge clk) disable iff (reset) (Q == 4'b1100) |-> (out_sum == (out_xor + 4'b1100))
    );
    // out_sum mapping when Q == 1000.
    check_out_sum_when_Q_1000: assert property (
        @(posedge clk) disable iff (reset) (Q == 4'b1000) |-> (out_sum == (out_xor + 4'b1000))
    );
    // out_sum default mapping when Q is not one of the listed cases (includes Q==0000).
    check_out_sum_default_otherwise_zero: assert property (
        @(posedge clk) disable iff (reset)
            (!(Q == 4'b0001 || Q == 4'b0011 || Q == 4'b0111 || Q == 4'b1111 || Q == 4'b1110 || Q == 4'b1100 || Q == 4'b1000))
            |-> (out_sum == 4'b0000)
    );
endmodule