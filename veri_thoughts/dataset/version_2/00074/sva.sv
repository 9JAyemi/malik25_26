module jAsynchronousCounter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count,
    input logic [3:0] countbar
);

    // While reset is high at a clk edge, the counter is cleared.
    check_reset_clears_counter: assert property (
        @(posedge clk) rst |-> ((count == 4'b0000) && (countbar == 4'b1111))
    );

    // countbar[0] is always the inverse of count[0].
    check_countbar0_is_complement: assert property (
        @(posedge clk or posedge rst) disable iff (rst) countbar[0] == ~count[0]
    );

    // countbar[1] is always the inverse of count[1].
    check_countbar1_is_complement: assert property (
        @(posedge count[0] or posedge rst) disable iff (rst) countbar[1] == ~count[1]
    );

    // countbar[2] is always the inverse of count[2].
    check_countbar2_is_complement: assert property (
        @(posedge count[1] or posedge rst) disable iff (rst) countbar[2] == ~count[2]
    );

    // countbar[3] is always the inverse of count[3].
    check_countbar3_is_complement: assert property (
        @(posedge count[2] or posedge rst) disable iff (rst) countbar[3] == ~count[3]
    );

    // Bit 0 loads its inverted feedback on each clk edge.
    check_count0_captures_inverted_feedback: assert property (
        @(posedge clk or posedge rst) disable iff (rst) 1'b1 |=> (count[0] == $past(countbar[0]))
    );

    // Bit 1 loads its inverted feedback on each posedge of count[0].
    check_count1_captures_inverted_feedback: assert property (
        @(posedge count[0] or posedge rst) disable iff (rst) 1'b1 |=> (count[1] == $past(countbar[1]))
    );

    // Bit 2 loads its inverted feedback on each posedge of count[1].
    check_count2_captures_inverted_feedback: assert property (
        @(posedge count[1] or posedge rst) disable iff (rst) 1'b1 |=> (count[2] == $past(countbar[2]))
    );

    // Bit 3 loads its inverted feedback on each posedge of count[2].
    check_count3_captures_inverted_feedback: assert property (
        @(posedge count[2] or posedge rst) disable iff (rst) 1'b1 |=> (count[3] == $past(countbar[3]))
    );

    // On each clk edge outside reset, the sampled count decrements by one.
    check_counter_decrements_each_clk: assert property (
        @(posedge clk or posedge rst) disable iff (rst) 1'b1 |=> (count == ($past(count) - 4'd1))
    );

endmodule