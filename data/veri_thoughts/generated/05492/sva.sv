module my_clock_gate_sva (
    input logic clk,
    input logic en,
    input logic te,
    input logic enclk
);

    // enclk updates according to the registered enable/te equation.
    check_enclk_next_state: assert property (
        @(posedge clk) 1'b1 |=> (enclk == ($past(en) ? $past(te) : $past(enclk)))
    );

    // An enabled cycle with te high drives enclk high on the next clock.
    check_enclk_set_when_enabled_and_te_high: assert property (
        @(posedge clk) en && te |=> enclk
    );

    // An enabled cycle with te low drives enclk low on the next clock.
    check_enclk_clear_when_enabled_and_te_low: assert property (
        @(posedge clk) en && !te |=> !enclk
    );

    // A disabled cycle leaves enclk unchanged.
    check_enclk_holds_when_disabled: assert property (
        @(posedge clk) !en |=> $stable(enclk)
    );

endmodule