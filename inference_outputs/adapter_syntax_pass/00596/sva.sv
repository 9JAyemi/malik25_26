module inverter_sva (
    input logic ip,
    input logic op,
    input logic clk,
    input logic ce,
    input logic clr
);

    // op is low whenever clr is asserted.
    check_op_low_when_clr_high: assert property (
        @(posedge clk) clr |-> (op == 1'b0)
    );

    // op is high when ce is high and ip is low.
    check_op_high_when_ce_and_ip_low: assert property (
        @(posedge clk) disable iff (clr) ce && !ip |-> (op == 1'b1)
    );

    // op is low when ce is high and ip is high.
    check_op_low_when_ce_and_ip_high: assert property (
        @(posedge clk) disable iff (clr) ce && ip |-> (op == 1'b0)
    );

    // op holds its value when ce is low.
    check_op_holds_when_ce_low: assert property (
        @(posedge clk) disable iff (clr) !ce |-> $stable(op)
    );

endmodule