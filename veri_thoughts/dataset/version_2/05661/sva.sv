module bridge_sva (
    input logic [7:0] RGA,
    input logic [0:0] RGB,
    input logic [7:0] OPT,
    input logic [1:0] KEY,
    input logic CLK,
    input logic RST,
    input logic ENA,
    input logic [7:0] RGZ,
    input logic [7:0] shift_reg,
    input logic [7:0] not_reg,
    input logic [7:0] zero_reg
);

    // Reset clears all registers and the output.
    check_reset_clears_state: assert property (
        @(posedge CLK)
        !RST |-> (shift_reg == 8'h00 && not_reg == 8'h00 && zero_reg == 8'h00 && RGZ == 8'h00)
    );

    // ENA low leaves all registers unchanged.
    check_hold_when_disabled: assert property (
        @(posedge CLK) disable iff (!RST)
        (!ENA) |=> ($stable(shift_reg) && $stable(not_reg) && $stable(zero_reg))
    );

    // OPT=0, KEY=2 updates shift_reg with a 1-bit left shift.
    check_shift_left_1: assert property (
        @(posedge CLK) disable iff (!RST)
        (ENA && OPT == 8'h00 && KEY == 2'b10) |=> (shift_reg == {$past(RGA[6:0]), 1'b0} &&
                                                    $stable(not_reg) &&
                                                    $stable(zero_reg))
    );

    // OPT=0, KEY=0 updates shift_reg with a 1-bit right shift.
    check_shift_right_1: assert property (
        @(posedge CLK) disable iff (!RST)
        (ENA && OPT == 8'h00 && KEY == 2'b00) |=> (shift_reg == {1'b0, $past(RGA[7:1])} &&
                                                    $stable(not_reg) &&
                                                    $stable(zero_reg))
    );

    // OPT=0, KEY=3 updates shift_reg with a 2-bit left shift.
    check_shift_left_2: assert property (
        @(posedge CLK) disable iff (!RST)
        (ENA && OPT == 8'h00 && KEY == 2'b11) |=> (shift_reg == {$past(RGA[5:0]), 2'b00} &&
                                                    $stable(not_reg) &&
                                                    $stable(zero_reg))
    );

    // OPT=0, KEY=1 updates shift_reg with a 2-bit right shift.
    check_shift_right_2: assert property (
        @(posedge CLK) disable iff (!RST)
        (ENA && OPT == 8'h00 && KEY == 2'b01) |=> (shift_reg == {2'b00, $past(RGA[7:2])} &&
                                                    $stable(not_reg) &&
                                                    $stable(zero_reg))
    );

    // OPT=1, KEY=0 updates not_reg with bitwise inversion of RGA.
    check_not_load: assert property (
        @(posedge CLK) disable iff (!RST)
        (ENA && OPT == 8'h01 && KEY == 2'b00) |=> (not_reg == ~$past(RGA) &&
                                                    $stable(shift_reg) &&
                                                    $stable(zero_reg))
    );

    // All other enabled cases load raw RGA into shift_reg.
    check_default_load: assert property (
        @(posedge CLK) disable iff (!RST)
        (ENA && !(OPT == 8'h00) && !((OPT == 8'h01) && (KEY == 2'b00))) |=> (shift_reg == $past(RGA) &&
                                                                               $stable(not_reg) &&
                                                                               $stable(zero_reg))
    );

    // RGB high selects not_reg onto RGZ.
    check_rgz_selects_not_reg: assert property (
        @(posedge CLK) disable iff (!RST)
        (RGB == 1'b1) |-> (RGZ == not_reg)
    );

    // RGB low with KEY=2 selects zero_reg onto RGZ.
    check_rgz_selects_zero_reg: assert property (
        @(posedge CLK) disable iff (!RST)
        (RGB == 1'b0 && KEY == 2'b10) |-> (RGZ == zero_reg)
    );

    // Otherwise RGZ reflects shift_reg.
    check_rgz_selects_shift_reg: assert property (
        @(posedge CLK) disable iff (!RST)
        (RGB == 1'b0 && KEY != 2'b10) |-> (RGZ == shift_reg)
    );

endmodule

bind bridge bridge_sva bridge_sva_i (
    .RGA(RGA),
    .RGB(RGB),
    .OPT(OPT),
    .KEY(KEY),
    .CLK(CLK),
    .RST(RST),
    .ENA(ENA),
    .RGZ(RGZ),
    .shift_reg(shift_reg),
    .not_reg(not_reg),
    .zero_reg(zero_reg)
);