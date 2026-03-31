module inverter_sva (
    input logic ip,
    input logic op,
    input logic clk,
    input logic ce,
    input logic clr
);

// op is 0 when clr is 1.
    check_clear_forces_zero: assert property (
        @(posedge clk) clr |-> (op == 1'b0)
    );

// With ce=1, op captures ~ip on the next clock.
    check_capture_inverted_when_ce_high: assert property (
        @(posedge clk) disable iff (clr) ce |=> (op == ~$past(ip))
    );

// With ce=0, op holds its previous value.
    check_hold_when_ce_low: assert property (
        @(posedge clk) disable iff (clr) !ce |=> (op == $past(op))
    );

// With ce=1, op equals ~ip on the next clock.
    check_next_cycle_matches_inversion_when_ce_high: assert property (
        @(posedge clk) disable iff (clr) ce |=> (op == ~$past(ip))
    );

// With ce=0, op equals previous ip on the next clock.
    check_next_cycle_matches_previous_ip_when_ce_low: assert property (
        @(posedge clk) disable iff (clr) !ce |=> (op == $past(ip))
    );

endmodule
