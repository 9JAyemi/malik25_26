module register_counter_sva (
    input logic        clk,
    input logic        reset,
    input logic        enable,
    input logic [7:0]  d,
    input logic [7:0]  q,
    input logic [11:0] out_final
);

    // Reset sets the register and counter state to the defined values.
    check_reset_sets_out_final: assert property (
        @(posedge clk) disable iff ($initstate)
        reset |=> (out_final == 12'h340)
    );

    // After reset, q reflects the reset state through the current mux select.
    check_reset_sets_q: assert property (
        @(posedge clk) disable iff ($initstate)
        reset |=> (q == (enable ? 8'h00 : 8'h34))
    );

    // When enabled, the counter increments on the next cycle.
    check_counter_increments_on_enable: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        enable |=> (out_final[3:0] == ($past(out_final[3:0]) + 4'd1))
    );

    // When enabled, the register value holds on the next cycle.
    check_register_holds_on_enable: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        enable |=> (out_final[11:4] == $past(out_final[11:4]))
    );

    // When disabled, the register loads d on the next cycle.
    check_register_loads_d_on_disable: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !enable |=> (out_final[11:4] == $past(d))
    );

    // When disabled, the counter holds on the next cycle.
    check_counter_holds_on_disable: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !enable |=> (out_final[3:0] == $past(out_final[3:0]))
    );

    // q selects the zero-extended counter when enable is high.
    check_q_selects_counter_when_enabled: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        enable |-> (q == {4'b0000, out_final[3:0]})
    );

    // q selects the register value when enable is low.
    check_q_selects_register_when_disabled: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !enable |-> (q == out_final[11:4])
    );

endmodule