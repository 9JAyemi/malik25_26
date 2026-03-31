module inverter_sva (
    input logic [0:0] ip,
    input logic [0:0] op,
    input logic       clk,
    input logic       ce,
    input logic       clr
);

    // op is forced low whenever clr is asserted.
    check_clear_forces_low: assert property (
        @(posedge clk) clr |-> (op == 1'b0)
    );

    // With ce high, op captures the inverted input on the next cycle.
    check_capture_inverts_input: assert property (
        @(posedge clk) disable iff (clr) ce |=> (op == ~$past(ip))
    );

    // With ce low, op holds its previous value.
    check_hold_when_ce_low: assert property (
        @(posedge clk) disable iff (clr) !ce |=> (op == $past(op))
    );

    // A change on op must come from a prior ce or a prior clr.
    check_output_change_has_valid_cause: assert property (
        @(posedge clk) disable iff (clr) $changed(op) |-> ($past(ce) || $past(clr))
    );

    // With ce high and ip stable, op remains stable.
    check_capture_ignores_stable_input: assert property (
        @(posedge clk) disable iff (clr) (ce && $stable(ip)) |=> $stable(op)
    );

endmodule