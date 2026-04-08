module four_bit_adder_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);

    // Reset forces outputs low on the next cycle.
    check_reset_clears_outputs: assert property (
        @(posedge clk) rst |=> (sum == 4'b0000 && cout == 1'b0)
    );

    // Sum reflects the previous cycle's registered addition.
    check_sum_matches_previous_inputs: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) |-> (sum == ($past(a) + $past(b) + $past(cin)))
    );

    // Cout reflects the previous cycle's registered MSB majority logic.
    check_cout_matches_previous_inputs: assert property (
        @(posedge clk) disable iff (rst)
            $past(!rst) |-> (cout == (($past(a[3]) & $past(b[3])) |
                                      ($past(a[3]) & $past(cin))  |
                                      ($past(b[3]) & $past(cin))))
    );

    // With b and cin low, sum passes through the previous a.
    check_a_passthrough_when_b_and_cin_zero: assert property (
        @(posedge clk) disable iff (rst)
            ($past(!rst) && ($past(b) == 4'b0000) && ($past(cin) == 1'b0))
            |-> (sum == $past(a) && cout == 1'b0)
    );

    // With a and cin low, sum passes through the previous b.
    check_b_passthrough_when_a_and_cin_zero: assert property (
        @(posedge clk) disable iff (rst)
            ($past(!rst) && ($past(a) == 4'b0000) && ($past(cin) == 1'b0))
            |-> (sum == $past(b) && cout == 1'b0)
    );

    // All-zero inputs produce all-zero outputs on the next cycle.
    check_zero_inputs_produce_zero_outputs: assert property (
        @(posedge clk) disable iff (rst)
            ($past(!rst) && ($past(a) == 4'b0000) && ($past(b) == 4'b0000) && ($past(cin) == 1'b0))
            |-> (sum == 4'b0000 && cout == 1'b0)
    );

    // High previous MSBs on a and b force cout high.
    check_cout_high_for_msb_pair: assert property (
        @(posedge clk) disable iff (rst)
            ($past(!rst) && $past(a[3]) && $past(b[3])) |-> (cout == 1'b1)
    );

    // Low previous MSBs and low cin force cout low.
    check_cout_low_for_zero_msb_inputs: assert property (
        @(posedge clk) disable iff (rst)
            ($past(!rst) && !$past(a[3]) && !$past(b[3]) && !$past(cin)) |-> (cout == 1'b0)
    );

endmodule