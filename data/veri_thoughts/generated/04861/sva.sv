module rsdec_syn_sva (
    input logic        clk,
    input logic        clrn,
    input logic        shift,
    input logic        init,
    input logic        enable,
    input logic [8:0]  u,
    input logic [8:0]  y0,
    input logic [8:0]  y1,
    input logic [8:0]  y2,
    input logic [8:0]  y3,
    input logic [8:0]  y4,
    input logic [8:0]  y5,
    input logic [8:0]  y6,
    input logic [8:0]  y7
);

    // Active-low synchronous reset clears all syndrome registers.
    check_reset_clears_regs: assert property (
        @(posedge clk)
        (!clrn) |=> (y0 == 9'h000) &&
                    (y1 == 9'h000) &&
                    (y2 == 9'h000) &&
                    (y3 == 9'h000) &&
                    (y4 == 9'h000) &&
                    (y5 == 9'h000) &&
                    (y6 == 9'h000) &&
                    (y7 == 9'h000)
    );

    // Init has priority and loads all registers with u.
    check_init_loads_all_regs: assert property (
        @(posedge clk) disable iff (!clrn)
        init |=> (y0 == $past(u)) &&
                 (y1 == $past(u)) &&
                 (y2 == $past(u)) &&
                 (y3 == $past(u)) &&
                 (y4 == $past(u)) &&
                 (y5 == $past(u)) &&
                 (y6 == $past(u)) &&
                 (y7 == $past(u))
    );

    // Enable updates each register with its fixed scale constant XOR u.
    check_enable_updates_scaled_xor: assert property (
        @(posedge clk) disable iff (!clrn)
        (!init && enable) |=> (y0 == ($past(u) ^ 9'h001)) &&
                              (y1 == ($past(u) ^ 9'h002)) &&
                              (y2 == ($past(u) ^ 9'h004)) &&
                              (y3 == ($past(u) ^ 9'h008)) &&
                              (y4 == ($past(u) ^ 9'h010)) &&
                              (y5 == ($past(u) ^ 9'h020)) &&
                              (y6 == ($past(u) ^ 9'h040)) &&
                              (y7 == ($past(u) ^ 9'h080))
    );

    // Shift rotates the register bank when no higher-priority control is active.
    check_shift_rotates_regs: assert property (
        @(posedge clk) disable iff (!clrn)
        (!init && !enable && shift) |=> (y0 == $past(y1)) &&
                                        (y1 == $past(y2)) &&
                                        (y2 == $past(y3)) &&
                                        (y3 == $past(y4)) &&
                                        (y4 == $past(y5)) &&
                                        (y5 == $past(y6)) &&
                                        (y6 == $past(y7)) &&
                                        (y7 == $past(y0))
    );

    // Registers hold their values when no control input is asserted.
    check_idle_holds_regs: assert property (
        @(posedge clk) disable iff (!clrn)
        (!init && !enable && !shift) |=> (y0 == $past(y0)) &&
                                         (y1 == $past(y1)) &&
                                         (y2 == $past(y2)) &&
                                         (y3 == $past(y3)) &&
                                         (y4 == $past(y4)) &&
                                         (y5 == $past(y5)) &&
                                         (y6 == $past(y6)) &&
                                         (y7 == $past(y7))
    );

endmodule