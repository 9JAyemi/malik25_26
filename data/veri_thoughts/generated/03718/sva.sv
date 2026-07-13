module up_down_counter_sva (
    input logic clk,
    input logic UP,
    input logic DOWN,
    input logic LOAD,
    input logic [3:0] DIN,
    input logic [3:0] Q,
    input logic [3:0] Q_reg1,
    input logic [3:0] Q_reg2,
    input logic [3:0] Q_reg3
);

    // Q is driven directly from Q_reg3.
    check_output_matches_reg3: assert property (
        @(posedge clk) Q == Q_reg3
    );

    // LOAD has highest priority and copies DIN into all registers.
    check_load_copies_din_to_regs: assert property (
        @(posedge clk)
        LOAD |=> (Q_reg1 == $past(DIN)) &&
                 (Q_reg2 == $past(DIN)) &&
                 (Q_reg3 == $past(DIN))
    );

    // LOAD also updates the visible output on the next cycle.
    check_load_updates_output: assert property (
        @(posedge clk)
        LOAD |=> (Q == $past(DIN))
    );

    // UP has priority over DOWN and increments all registers when not at 15.
    check_up_increments_regs: assert property (
        @(posedge clk)
        (!LOAD && UP && (Q_reg1 != 4'hF)) |=> (Q_reg1 == ($past(Q_reg1) + 4'h1)) &&
                                              (Q_reg2 == ($past(Q_reg2) + 4'h1)) &&
                                              (Q_reg3 == ($past(Q_reg3) + 4'h1))
    );

    // UP wraps all registers to 0 when Q_reg1 is 15.
    check_up_wraps_regs: assert property (
        @(posedge clk)
        (!LOAD && UP && (Q_reg1 == 4'hF)) |=> (Q_reg1 == 4'h0) &&
                                              (Q_reg2 == 4'h0) &&
                                              (Q_reg3 == 4'h0)
    );

    // DOWN decrements all registers when selected and Q_reg1 is not 0.
    check_down_decrements_regs: assert property (
        @(posedge clk)
        (!LOAD && !UP && DOWN && (Q_reg1 != 4'h0)) |=> (Q_reg1 == ($past(Q_reg1) - 4'h1)) &&
                                                       (Q_reg2 == ($past(Q_reg2) - 4'h1)) &&
                                                       (Q_reg3 == ($past(Q_reg3) - 4'h1))
    );

    // DOWN wraps all registers to 15 when Q_reg1 is 0.
    check_down_wraps_regs: assert property (
        @(posedge clk)
        (!LOAD && !UP && DOWN && (Q_reg1 == 4'h0)) |=> (Q_reg1 == 4'hF) &&
                                                       (Q_reg2 == 4'hF) &&
                                                       (Q_reg3 == 4'hF)
    );

    // With no active control, all registers hold their value.
    check_hold_without_controls: assert property (
        @(posedge clk)
        (!LOAD && !UP && !DOWN) |=> (Q_reg1 == $past(Q_reg1)) &&
                                    (Q_reg2 == $past(Q_reg2)) &&
                                    (Q_reg3 == $past(Q_reg3))
    );

endmodule