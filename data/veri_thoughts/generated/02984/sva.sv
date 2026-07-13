module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] q
);
    // When reset is asserted LOW at a clock edge, q must be 0.
    check_reset_forces_zero: assert property (
        @(posedge clk) !rst |-> (q == 4'h0)
    );

    // On reset deassertion (LOW->HIGH) at a clock edge, q moves from 0 to 1.
    check_q_is_one_on_reset_release: assert property (
        @(posedge clk) $rose(rst) |-> (q == 4'h1)
    );

    // If previous q was 0xF and reset is HIGH at consecutive edges, q is 0 (normal wrap) or 1 (reset glitch then increment).
    check_wrap_or_reset_after_prev_F: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) && ($past(q) == 4'hF) && rst |-> (q == 4'h0) || (q == 4'h1)
    );

    // When out of reset at consecutive edges, q==0 can only come from previous q==0xF.
    check_zero_only_after_prev_F: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) && rst && (q == 4'h0) |-> ($past(q) == 4'hF)
    );

    // When out of reset at consecutive edges, q cannot remain 0xF.
    check_no_F_repeat_without_reset: assert property (
        @(posedge clk) disable iff (!rst) $past(rst) && rst && ($past(q) == 4'hF) |-> (q != 4'hF)
    );
endmodule