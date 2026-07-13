module clock_counter_sva (
    input logic clk_i,
    input logic reset_n,
    input logic clk_o,
    input logic [14:0] count
);
    // Asynchronous reset drives clk_o and count to 0.
    reset_forces_zero: assert property (
        @(posedge clk_i) !reset_n |-> (clk_o == 1'b0) && (count == 15'd0)
    );

    // Outside reset, count never exceeds 5000.
    count_never_above_threshold: assert property (
        @(posedge clk_i) disable iff (!reset_n) (count <= 15'd5000)
    );

    // When count < 5000, it increments by exactly 1 on the next cycle.
    count_increments_when_below_threshold: assert property (
        @(posedge clk_i) disable iff (!reset_n) (count < 15'd5000) |=> (count == $past(count) + 15'd1)
    );

    // When count < 5000, clk_o holds its previous value.
    clk_o_stable_when_below_threshold: assert property (
        @(posedge clk_i) disable iff (!reset_n) (count < 15'd5000) |=> (clk_o == $past(clk_o))
    );

    // When count >= 5000, clk_o toggles on the next cycle.
    clk_o_toggles_on_threshold: assert property (
        @(posedge clk_i) disable iff (!reset_n) (count >= 15'd5000) |=> (clk_o == ~$past(clk_o))
    );

    // When count >= 5000, count clears to 0 on the next cycle.
    count_clears_on_threshold: assert property (
        @(posedge clk_i) disable iff (!reset_n) (count >= 15'd5000) |=> (count == 15'd0)
    );

    // Any change on clk_o must be caused by a prior threshold event.
    clko_change_caused_by_threshold: assert property (
        @(posedge clk_i) disable iff (!reset_n) $changed(clk_o) |-> ($past(count) >= 15'd5000)
    );

    // If prior count was below 5000, clk_o must not change this cycle.
    no_clko_change_when_prev_below_threshold: assert property (
        @(posedge clk_i) disable iff (!reset_n) ($past(count) < 15'd5000) |-> (!$changed(clk_o))
    );

    // If count is 0 (out of reset), the previous cycle was reset or a threshold event.
    zero_count_has_valid_cause: assert property (
        @(posedge clk_i) disable iff (!reset_n) (count == 15'd0) |-> (!$past(reset_n) || ($past(count) >= 15'd5000))
    );

    // When count is 0 (out of reset), it advances to 1 on the next cycle.
    zero_advances_to_one_next: assert property (
        @(posedge clk_i) disable iff (!reset_n) (count == 15'd0) |=> (count == 15'd1)
    );
endmodule