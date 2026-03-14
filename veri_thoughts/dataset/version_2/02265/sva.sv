module clock_divider_sva (
    input logic clk_in,
    input logic clk_out_1,
    input logic clk_out_2,
    input logic clk_out_3,
    input logic [25:0] counter_25,
    input logic [26:0] counter_12_5,
    input logic [27:0] counter_6_25
);

    ///// counter_25 behavior /////
    // When not at terminal count, counter_25 increments by 1.
    check_counter25_increment_nonwrap: assert property (
        @(posedge clk_in) ($past(counter_25) != 26'd999999) |-> (counter_25 == $past(counter_25) + 26'd1)
    );
    // When reaching terminal count, counter_25 wraps to 0.
    check_counter25_wrap_to_zero: assert property (
        @(posedge clk_in) ($past(counter_25) == 26'd999999) |-> (counter_25 == 26'd0)
    );

    ///// counter_12_5 behavior /////
    // When not at terminal count, counter_12_5 increments by 1.
    check_counter12_5_increment_nonwrap: assert property (
        @(posedge clk_in) ($past(counter_12_5) != 27'd1999999) |-> (counter_12_5 == $past(counter_12_5) + 27'd1)
    );
    // When reaching terminal count, counter_12_5 wraps to 0.
    check_counter12_5_wrap_to_zero: assert property (
        @(posedge clk_in) ($past(counter_12_5) == 27'd1999999) |-> (counter_12_5 == 27'd0)
    );

    ///// counter_6_25 behavior /////
    // When not at terminal count, counter_6_25 increments by 1.
    check_counter6_25_increment_nonwrap: assert property (
        @(posedge clk_in) ($past(counter_6_25) != 28'd3999999) |-> (counter_6_25 == $past(counter_6_25) + 28'd1)
    );
    // When reaching terminal count, counter_6_25 wraps to 0.
    check_counter6_25_wrap_to_zero: assert property (
        @(posedge clk_in) ($past(counter_6_25) == 28'd3999999) |-> (counter_6_25 == 28'd0)
    );

    ///// clk_out_1 behavior /////
    // clk_out_1 can change only when counter_25 hit terminal count in the previous cycle.
    check_out1_change_requires_counter25_wrap: assert property (
        @(posedge clk_in) $changed(clk_out_1) |-> ($past(counter_25) == 26'd999999)
    );
    // When counter_25 hit terminal count and previous clk_out_1 was known, clk_out_1 toggles.
    check_out1_toggle_on_wrap_when_known: assert property (
        @(posedge clk_in) (($past(counter_25) == 26'd999999) && (!$isunknown($past(clk_out_1)))) |-> (clk_out_1 == ~$past(clk_out_1))
    );
    // When counter_25 did not hit terminal count and previous clk_out_1 was known, clk_out_1 holds.
    check_out1_stable_when_no_wrap_when_known: assert property (
        @(posedge clk_in) (($past(counter_25) != 26'd999999) && (!$isunknown($past(clk_out_1)))) |-> (clk_out_1 == $past(clk_out_1))
    );

    ///// clk_out_2 behavior /////
    // clk_out_2 can change only when counter_12_5 hit terminal count in the previous cycle.
    check_out2_change_requires_counter12_5_wrap: assert property (
        @(posedge clk_in) $changed(clk_out_2) |-> ($past(counter_12_5) == 27'd1999999)
    );
    // When counter_12_5 hit terminal count and previous clk_out_2 was known, clk_out_2 toggles.
    check_out2_toggle_on_wrap_when_known: assert property (
        @(posedge clk_in) (($past(counter_12_5) == 27'd1999999) && (!$isunknown($past(clk_out_2)))) |-> (clk_out_2 == ~$past(clk_out_2))
    );
    // When counter_12_5 did not hit terminal count and previous clk_out_2 was known, clk_out_2 holds.
    check_out2_stable_when_no_wrap_when_known: assert property (
        @(posedge clk_in) (($past(counter_12_5) != 27'd1999999) && (!$isunknown($past(clk_out_2)))) |-> (clk_out_2 == $past(clk_out_2))
    );

    ///// clk_out_3 behavior /////
    // clk_out_3 can change only when counter_6_25 hit terminal count in the previous cycle.
    check_out3_change_requires_counter6_25_wrap: assert property (
        @(posedge clk_in) $changed(clk_out_3) |-> ($past(counter_6_25) == 28'd3999999)
    );
    // When counter_6_25 hit terminal count and previous clk_out_3 was known, clk_out_3 toggles.
    check_out3_toggle_on_wrap_when_known: assert property (
        @(posedge clk_in) (($past(counter_6_25) == 28'd3999999) && (!$isunknown($past(clk_out_3)))) |-> (clk_out_3 == ~$past(clk_out_3))
    );
    // When counter_6_25 did not hit terminal count and previous clk_out_3 was known, clk_out_3 holds.
    check_out3_stable_when_no_wrap_when_known: assert property (
        @(posedge clk_in) (($past(counter_6_25) != 28'd3999999) && (!$isunknown($past(clk_out_3)))) |-> (clk_out_3 == $past(clk_out_3))
    );

endmodule