module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] ena,
    input logic [7:0] q
);

    // Synchronous reset clears both outputs on the next clock.
    reset_clears_outputs: assert property (
        @(posedge clk) reset |=> (q == 8'h00) && (ena == 4'h0)
    );

    // The multiplier output always has a zero low nibble.
    check_q_low_nibble_zero: assert property (
        @(posedge clk) disable iff (reset) q[3:0] == 4'h0
    );

    // The enable output matches the encoder function of q[7:4].
    check_ena_matches_encoder: assert property (
        @(posedge clk) disable iff (reset) ena == {2'b00, (|q[7:6]), (|q[5:4])}
    );

    // BCD 0 advances to 1.
    check_count_0_to_1: assert property (
        @(posedge clk) disable iff (reset) (q == 8'h00) |=> (q == 8'h10)
    );

    // BCD 1 advances to 2.
    check_count_1_to_2: assert property (
        @(posedge clk) disable iff (reset) (q == 8'h10) |=> (q == 8'h20)
    );

    // BCD 2 advances to 3.
    check_count_2_to_3: assert property (
        @(posedge clk) disable iff (reset) (q == 8'h20) |=> (q == 8'h30)
    );

    // BCD 3 advances to 4.
    check_count_3_to_4: assert property (
        @(posedge clk) disable iff (reset) (q == 8'h30) |=> (q == 8'h40)
    );

    // BCD 4 advances to 5.
    check_count_4_to_5: assert property (
        @(posedge clk) disable iff (reset) (q == 8'h40) |=> (q == 8'h50)
    );

    // BCD 5 advances to 6.
    check_count_5_to_6: assert property (
        @(posedge clk) disable iff (reset) (q == 8'h50) |=> (q == 8'h60)
    );

    // BCD 6 advances to 7.
    check_count_6_to_7: assert property (
        @(posedge clk) disable iff (reset) (q == 8'h60) |=> (q == 8'h70)
    );

    // BCD 7 advances to 8.
    check_count_7_to_8: assert property (
        @(posedge clk) disable iff (reset) (q == 8'h70) |=> (q == 8'h80)
    );

    // BCD 8 advances to 9.
    check_count_8_to_9: assert property (
        @(posedge clk) disable iff (reset) (q == 8'h80) |=> (q == 8'h90)
    );

    // BCD 9 wraps back to 0.
    check_count_9_to_0: assert property (
        @(posedge clk) disable iff (reset) (q == 8'h90) |=> (q == 8'h00)
    );

    // An invalid counter digit recovers to zero.
    check_invalid_digit_recovers_to_zero: assert property (
        @(posedge clk) disable iff (reset) (q[3:0] == 4'h0) && (q[7:4] > 4'd9) |=> (q == 8'h00)
    );

endmodule