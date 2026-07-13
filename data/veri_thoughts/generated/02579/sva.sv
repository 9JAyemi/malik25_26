module binary_counter_sva (
    input logic clk,
    input logic [7:0] max_count,
    input logic [7:0] count
);
    // Clock: clk (posedge). No reset in RTL; sequential: if (count==max_count) -> 0 else +1 (mod 256).

    // If previous count equaled previous max_count, next count is 0.
    update_to_zero_on_match: assert property (
        @(posedge clk) ($past(count) == $past(max_count)) |-> (count == 8'h00)
    );

    // If previous count did not equal previous max_count, next count increments by 1 (mod 256).
    update_increment_on_no_match: assert property (
        @(posedge clk) ($past(count) != $past(max_count)) |-> (count == ($past(count) + 8'd1)[7:0])
    );

    // If current count is 0, it must be due to a previous match or an overflow from 0xFF.
    zero_implies_from_match_or_overflow: assert property (
        @(posedge clk) (count == 8'h00) |-> (($past(count) == $past(max_count)) || ($past(count) == 8'hFF))
    );

    // If previous was 0xFF and did not match max_count, overflow to 0 occurs.
    overflow_to_zero_when_prev_ff_no_match: assert property (
        @(posedge clk) (($past(count) == 8'hFF) && ($past(count) != $past(max_count))) |-> (count == 8'h00)
    );

    // If previous was not 0xFF and did not match max_count, next value cannot be 0.
    no_spurious_zero_without_ff_no_match: assert property (
        @(posedge clk) (($past(count) != $past(max_count)) && ($past(count) != 8'hFF)) |-> (count != 8'h00)
    );

    // Over two consecutive non-match cycles, count increases by 2 (mod 256).
    two_cycle_increment_without_match: assert property (
        @(posedge clk) (($past(count,2) != $past(max_count,2)) && ($past(count,1) != $past(max_count,1)))
        |-> (count == ($past(count,2) + 8'd2)[7:0])
    );

    // If previous matched max_count and current max_count is 0, count remains 0 (idempotent reset to 0).
    zero_sticky_when_max_zero: assert property (
        @(posedge clk) (($past(count) == $past(max_count)) && (max_count == 8'h00)) |-> (count == 8'h00)
    );

    // If previous count was 0 and previous max_count was nonzero, next count becomes 1.
    from_zero_when_max_nonzero: assert property (
        @(posedge clk) (($past(count) == 8'h00) && ($past(max_count) != 8'h00)) |-> (count == 8'h01)
    );

endmodule