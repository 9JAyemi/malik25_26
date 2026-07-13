module my_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] output1,
    input logic [3:0] output2,
    input logic signed [31:0] count
);
    // After a cycle with reset=1, count becomes 0 on the next clock.
    check_count_resets_next: assert property (
        @(posedge clk) reset |=> (count == 32'sd0)
    );

    // After a cycle with reset=1, outputs become 0 and 4'hF on the next clock.
    check_outputs_reset_next: assert property (
        @(posedge clk) reset |=> (output1 == 4'd0) && (output2 == 4'hF)
    );

    // When out of reset for two consecutive cycles, count increments by 1 each clock.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (count == $past(count) + 32'sd1)
    );

    // When out of reset for two consecutive cycles, output1 increments by 1 modulo 16.
    check_output1_increments_mod16: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (output1 == $past(output1) + 4'd1)
    );

    // output2 is always the bitwise complement of output1.
    check_outputs_complement: assert property (
        @(posedge clk) disable iff (reset) (output2 == ~output1)
    );

    // output1 equals the low 4 bits of count.
    check_output1_matches_count_lsb: assert property (
        @(posedge clk) disable iff (reset) (output1 == count[3:0])
    );

    // output2 equals the bitwise NOT of the low 4 bits of count.
    check_output2_matches_not_count_lsb: assert property (
        @(posedge clk) disable iff (reset) (output2 == ~count[3:0])
    );

    // When out of reset for two consecutive cycles, output2 decrements by 1 modulo 16.
    check_output2_decrements_mod16: assert property (
        @(posedge clk) disable iff (reset) $past(!reset) |-> (output2 == $past(output2) - 4'd1)
    );

    // The XOR of output1 and output2 is always all 1s (complementary).
    check_outputs_xor_all_ones: assert property (
        @(posedge clk) disable iff (reset) ((output1 ^ output2) == 4'hF)
    );
endmodule