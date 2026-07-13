module shift_reg_sva (
    input logic CLK,
    input logic RST,
    input logic LD,
    input logic [3:0] D,
    input logic [3:0] OUT
);

    // OUT is the previous cycle's reg4 value.
    check_out_matches_prev_reg4: assert property (
        @(posedge CLK) disable iff (RST)
        1'b1 |=> (OUT == $past(reg4))
    );

    // A reset cycle clears reg4 by the next clock.
    check_reset_clears_reg4: assert property (
        @(posedge CLK)
        RST |=> (reg4 == 4'b0000)
    );

    // A load cycle captures D into reg1.
    check_load_captures_d_into_reg1: assert property (
        @(posedge CLK) disable iff (RST)
        LD |=> (reg1 == $past(D))
    );

    // A load cycle captures reg1 into reg2.
    check_load_captures_reg1_into_reg2: assert property (
        @(posedge CLK) disable iff (RST)
        LD |=> (reg2 == $past(reg1))
    );

    // A load cycle captures reg2 into reg3.
    check_load_captures_reg2_into_reg3: assert property (
        @(posedge CLK) disable iff (RST)
        LD |=> (reg3 == $past(reg2))
    );

    // A load cycle captures reg3 into reg4.
    check_load_captures_reg3_into_reg4: assert property (
        @(posedge CLK) disable iff (RST)
        LD |=> (reg4 == $past(reg3))
    );

    // A shift cycle moves reg2 into reg1.
    check_shift_moves_reg2_into_reg1: assert property (
        @(posedge CLK) disable iff (RST)
        !LD |=> (reg1 == $past(reg2))
    );

    // A shift cycle moves reg3 into reg2.
    check_shift_moves_reg3_into_reg2: assert property (
        @(posedge CLK) disable iff (RST)
        !LD |=> (reg2 == $past(reg3))
    );

    // A shift cycle moves reg4 into reg3.
    check_shift_moves_reg4_into_reg3: assert property (
        @(posedge CLK) disable iff (RST)
        !LD |=> (reg3 == $past(reg4))
    );

    // A shift cycle leaves reg4 unchanged.
    check_shift_holds_reg4: assert property (
        @(posedge CLK) disable iff (RST)
        !LD |=> (reg4 == $past(reg4))
    );

endmodule