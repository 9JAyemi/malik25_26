module shift_register_sva (
    input logic clk,
    input logic [3:0] D,
    input logic SI,
    input logic SO,
    // Internal DUT signals
    input logic [3:0] reg1,
    input logic [3:0] reg2,
    input logic [3:0] reg3,
    input logic [3:0] reg4
);
    // reg1 loads D when SI is high.
    check_reg1_load_on_SI_high: assert property (
        @(posedge clk) (SI == 1'b1) |=> (reg1 === $past(D))
    );

    // reg1 holds its value when SI is low.
    check_reg1_hold_on_SI_low: assert property (
        @(posedge clk) (SI == 1'b0) |=> (reg1 === $past(reg1))
    );

    // reg2 samples reg1 every cycle.
    check_reg2_samples_reg1: assert property (
        @(posedge clk) 1'b1 |=> (reg2 === $past(reg1))
    );

    // reg3 samples reg2 every cycle.
    check_reg3_samples_reg2: assert property (
        @(posedge clk) 1'b1 |=> (reg3 === $past(reg2))
    );

    // reg4 samples reg3 every cycle.
    check_reg4_samples_reg3: assert property (
        @(posedge clk) 1'b1 |=> (reg4 === $past(reg3))
    );

    // SO outputs the previous reg4[0] each cycle.
    check_SO_samples_reg4_lsb: assert property (
        @(posedge clk) 1'b1 |=> (SO === $past(reg4[0]))
    );

    // If reg1 changes, it must be due to SI high and equals prior D.
    check_reg1_change_implies_SI_and_D: assert property (
        @(posedge clk) $changed(reg1) |-> ($past(SI) && (reg1 === $past(D)))
    );

    // When SI is high, D[0] appears at SO after 4 cycles.
    check_D0_reaches_SO_in_4_cycles: assert property (
        @(posedge clk) (SI == 1'b1) |-> ##4 (SO === $past(D[0], 4))
    );

    // If SO changes, reg4[0] must have changed in the previous cycle.
    check_SO_change_follows_reg4_lsb_change: assert property (
        @(posedge clk) $changed(SO) |-> $past($changed(reg4[0]))
    );
endmodule