module shift_reg_sva (
    input logic       CLK,
    input logic       RST,
    input logic       LD,
    input logic [3:0] D,
    input logic [3:0] OUT
);

    // Reset clears the visible output on the following cycle.
    check_out_zero_after_reset: assert property (
        @(posedge CLK) disable iff (RST)
        $past(RST) |-> (OUT == 4'b0000)
    );

    // When load is low, the output holds its value.
    check_out_holds_when_ld_low: assert property (
        @(posedge CLK) disable iff (RST)
        !LD |=> (OUT == $past(OUT))
    );

    // Any output change must be caused by a load on the prior cycle.
    check_out_change_requires_prior_load: assert property (
        @(posedge CLK) disable iff (RST)
        (!$past(RST) && (OUT != $past(OUT))) |-> $past(LD)
    );

    // One load after reset is not enough to reach the output.
    check_out_zero_after_one_load_from_reset: assert property (
        @(posedge CLK) disable iff (RST)
        ($past(RST,2) && !$past(RST,1) && $past(LD,1)) |-> (OUT == 4'b0000)
    );

    // Two loads after reset are still not enough to reach the output.
    check_out_zero_after_two_loads_from_reset: assert property (
        @(posedge CLK) disable iff (RST)
        ($past(RST,3) && !$past(RST,2) && !$past(RST,1) &&
         $past(LD,2) && $past(LD,1)) |-> (OUT == 4'b0000)
    );

    // Three loads after reset are still not enough to reach the output.
    check_out_zero_after_three_loads_from_reset: assert property (
        @(posedge CLK) disable iff (RST)
        ($past(RST,4) && !$past(RST,3) && !$past(RST,2) && !$past(RST,1) &&
         $past(LD,3) && $past(LD,2) && $past(LD,1)) |-> (OUT == 4'b0000)
    );

    // Four consecutive loads delay D to OUT by four clocks.
    check_out_matches_d_after_four_loads: assert property (
        @(posedge CLK) disable iff (RST)
        (!$past(RST,4) && !$past(RST,3) && !$past(RST,2) && !$past(RST,1) &&
         $past(LD,4) && $past(LD,3) && $past(LD,2) && $past(LD,1)) |-> (OUT == $past(D,4))
    );

endmodule