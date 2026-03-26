module DECODER_sva (
    input logic clk,
    input logic INA,
    input logic INB,
    input logic INC,
    input logic TWOPOS,
    input logic TWONEG,
    input logic ONEPOS,
    input logic ONENEG
);

    // TWOPOS follows its combinational equation.
    check_twopos_equation: assert property (
        @(posedge clk) TWOPOS == ~(INA & INB & (~INC))
    );

    // TWONEG follows its combinational equation.
    check_twoneg_equation: assert property (
        @(posedge clk) TWONEG == ~(~((~INA) & (~INB) & INC))
    );

    // ONEPOS follows its combinational equation.
    check_onepos_equation: assert property (
        @(posedge clk) ONEPOS == (((~INA) & INB & (~INC)) | ((~INC) & (~INB) & INA))
    );

    // ONENEG follows its combinational equation.
    check_oneneg_equation: assert property (
        @(posedge clk) ONENEG == ((INA & (~INB) & INC) | (INC & INB & (~INA)))
    );

    // ONEPOS and ONENEG are never high together.
    check_one_outputs_mutually_exclusive: assert property (
        @(posedge clk) !(ONEPOS && ONENEG)
    );

    // Any one-magnitude output requires INA and INB to differ.
    check_one_outputs_require_input_mismatch: assert property (
        @(posedge clk) (ONEPOS || ONENEG) |-> (INA ^ INB)
    );

    // Matching INA and INB clear both one-magnitude outputs.
    check_equal_inputs_clear_one_outputs: assert property (
        @(posedge clk) !(INA ^ INB) |-> (!ONEPOS && !ONENEG)
    );

    // ONEPOS can only be high when INC is low.
    check_onepos_only_when_inc_low: assert property (
        @(posedge clk) ONEPOS |-> !INC
    );

    // ONENEG can only be high when INC is high.
    check_oneneg_only_when_inc_high: assert property (
        @(posedge clk) ONENEG |-> INC
    );

    // TWOPOS is low only for INA=1, INB=1, INC=0.
    check_twopos_low_only_for_110: assert property (
        @(posedge clk) !TWOPOS |-> (INA && INB && !INC)
    );

    // TWONEG is high only for INA=0, INB=0, INC=1.
    check_twoneg_high_only_for_001: assert property (
        @(posedge clk) TWONEG |-> (!INA && !INB && INC)
    );

endmodule