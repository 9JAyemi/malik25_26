module wait_generator_sva (
    input logic clk,
    input logic nreset,
    input logic WAIT,
    input logic wait_random,
    input logic [8:0] wait_counter
);
    // Clock: clk; Reset: nreset active-low
    // Mixed: sequential 9-bit counter + combinational wait_random
    // Behavior: wait_random = WAIT && (wait_counter[5:0] != 0)

    // Counter goes to 0 when reset falls.
    reset_fall_clears_counter: assert property (
        @(posedge clk) $fell(nreset) |-> (wait_counter == 9'b0)
    );

    // Counter becomes 1 on first clock after reset deassertion.
    counter_one_after_reset_release: assert property (
        @(posedge clk) $rose(nreset) |-> (wait_counter == 9'd1)
    );

    // Counter increments by 1 each cycle when out of reset.
    counter_increments_when_active: assert property (
        @(posedge clk) disable iff (!nreset) $past(nreset) |-> (wait_counter == $past(wait_counter) + 9'd1)
    );

    // Counter wraps from 9'h1FF to 0 when active.
    counter_wraps_after_max: assert property (
        @(posedge clk) disable iff (!nreset) $past(nreset) && ($past(wait_counter) == 9'h1FF) |-> (wait_counter == 9'h000)
    );

    // wait_random equals WAIT && (wait_counter[5:0] != 0) when active.
    wait_random_comb_function: assert property (
        @(posedge clk) disable iff (!nreset) wait_random == (WAIT && (wait_counter[5:0] != 6'b0))
    );

    // If WAIT is 0, wait_random must be 0 when active.
    wait_random_low_when_WAIT_low: assert property (
        @(posedge clk) disable iff (!nreset) (WAIT == 1'b0) |-> (wait_random == 1'b0)
    );

    // wait_random can only rise when WAIT is 1 and counter[5:0] is nonzero.
    wait_random_rise_condition: assert property (
        @(posedge clk) disable iff (!nreset) $rose(wait_random) |-> (WAIT == 1'b1) && (wait_counter[5:0] != 6'b0)
    );

    // wait_random can only fall when WAIT is 0 or counter[5:0] is zero.
    wait_random_fall_condition: assert property (
        @(posedge clk) disable iff (!nreset) $fell(wait_random) |-> ((WAIT == 1'b0) || (wait_counter[5:0] == 6'b0))
    );

endmodule