module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:1] ena,
    input logic [15:0] q
);

    // ena is the inversion of a constant 3'b111, so it stays zero.
    check_ena_constant_zero: assert property (
        @(posedge clk) disable iff (reset)
        (ena == 3'b000)
    );

    // q only drives the upper nibble; the lower 12 bits are always zero.
    check_q_lower_bits_zero: assert property (
        @(posedge clk) disable iff (reset)
        (q[11:0] == 12'b0)
    );

    // The upper nibble of q is always a decimal value from 0 to 9.
    check_q_upper_nibble_decimal: assert property (
        @(posedge clk) disable iff (reset)
        (q[15:12] <= 4'd9)
    );

    // Synchronous reset clears the visible outputs by the next clock.
    check_reset_clears_outputs: assert property (
        @(posedge clk)
        reset |=> ((q == 16'h0000) && (ena == 3'b000))
    );

    // ena remains zero even in cycles where reset is asserted.
    check_reset_keeps_ena_zero: assert property (
        @(posedge clk)
        reset |-> (ena == 3'b000)
    );

    // A displayed 0 either stays 0 in the default range or advances to 1 from count 0.
    check_q_zero_next_zero_or_one: assert property (
        @(posedge clk) disable iff (reset)
        (q[15:12] == 4'd0) |=> ((q[15:12] == 4'd0) || (q[15:12] == 4'd1))
    );

    // A displayed 1 advances to 2 on the next clock.
    check_q_one_to_two: assert property (
        @(posedge clk) disable iff (reset)
        (q[15:12] == 4'd1) |=> (q[15:12] == 4'd2)
    );

    // A displayed 2 advances to 3 on the next clock.
    check_q_two_to_three: assert property (
        @(posedge clk) disable iff (reset)
        (q[15:12] == 4'd2) |=> (q[15:12] == 4'd3)
    );

    // A displayed 3 advances to 4 on the next clock.
    check_q_three_to_four: assert property (
        @(posedge clk) disable iff (reset)
        (q[15:12] == 4'd3) |=> (q[15:12] == 4'd4)
    );

    // A displayed 4 advances to 5 on the next clock.
    check_q_four_to_five: assert property (
        @(posedge clk) disable iff (reset)
        (q[15:12] == 4'd4) |=> (q[15:12] == 4'd5)
    );

    // A displayed 5 advances to 6 on the next clock.
    check_q_five_to_six: assert property (
        @(posedge clk) disable iff (reset)
        (q[15:12] == 4'd5) |=> (q[15:12] == 4'd6)
    );

    // A displayed 6 advances to 7 on the next clock.
    check_q_six_to_seven: assert property (
        @(posedge clk) disable iff (reset)
        (q[15:12] == 4'd6) |=> (q[15:12] == 4'd7)
    );

    // A displayed 7 advances to 8 on the next clock.
    check_q_seven_to_eight: assert property (
        @(posedge clk) disable iff (reset)
        (q[15:12] == 4'd7) |=> (q[15:12] == 4'd8)
    );

    // A displayed 8 advances to 9, or to 0 after the last explicit table entry.
    check_q_eight_to_nine_or_zero: assert property (
        @(posedge clk) disable iff (reset)
        (q[15:12] == 4'd8) |=> ((q[15:12] == 4'd9) || (q[15:12] == 4'd0))
    );

    // A displayed 9 advances to 1 on the next clock.
    check_q_nine_to_one: assert property (
        @(posedge clk) disable iff (reset)
        (q[15:12] == 4'd9) |=> (q[15:12] == 4'd1)
    );

endmodule