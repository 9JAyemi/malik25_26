module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);
    // Clock: clk (posedge). Reset: rst (active-high, asynchronous). Logic: sequential counter with wrap to 0 at 15.

    // After reset deassertion, count is 0 on that sampled clock edge.
    check_count_zero_on_reset_release: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (count == 4'd0)
    );

    // When not at max (15), count increments by 1 on the next clock.
    check_increment_when_not_max: assert property (
        @(posedge clk) disable iff (rst) (count != 4'hF) |=> (count == $past(count) + 4'd1)
    );

    // When at max (15), count wraps to 0 on the next clock.
    check_wrap_when_max: assert property (
        @(posedge clk) disable iff (rst) (count == 4'hF) |=> (count == 4'd0)
    );

    // Every cycle out of reset, the transition is either +1 or wrap-to-0 from 15.
    check_valid_transition_each_cycle: assert property (
        @(posedge clk) disable iff (rst)
            1'b1 |=> ((($past(count) != 4'hF) && (count == $past(count) + 4'd1)) ||
                      (($past(count) == 4'hF) && (count == 4'd0)))
    );

    // From reset release, the counter produces the full 0..15..0 sequence if reset stays low.
    check_full_sequence_from_reset_release: assert property (
        @(posedge clk) disable iff (rst)
            $fell(rst) |-> (count == 4'd0)
                        ##1 (count == 4'd1)
                        ##1 (count == 4'd2)
                        ##1 (count == 4'd3)
                        ##1 (count == 4'd4)
                        ##1 (count == 4'd5)
                        ##1 (count == 4'd6)
                        ##1 (count == 4'd7)
                        ##1 (count == 4'd8)
                        ##1 (count == 4'd9)
                        ##1 (count == 4'd10)
                        ##1 (count == 4'd11)
                        ##1 (count == 4'd12)
                        ##1 (count == 4'd13)
                        ##1 (count == 4'd14)
                        ##1 (count == 4'd15)
                        ##1 (count == 4'd0)
    );

endmodule