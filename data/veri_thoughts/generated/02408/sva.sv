module Encoder_sva (
    input  logic CLK,
    input  logic Run,
    input  logic R1in,  input  logic R1out,
    input  logic R2in,  input  logic R2out,
    input  logic Add,   input  logic Sub,   input  logic Mul, input  logic Div,
    input  logic SelectY, input logic Yin,
    input  logic Zin,   input  logic Zout,
    input  logic End,
    input  logic [15:0] T,
    input  logic [3:0]  Ins
);
    // Run is tied HIGH.
    check_run_const: assert property (
        @(posedge CLK) Run === 1'b1
    );

    // R1in reflects T[0].
    check_r1in_map: assert property (
        @(posedge CLK) R1in === T[0]
    );

    // R1out reflects T[2].
    check_r1out_map: assert property (
        @(posedge CLK) R1out === T[2]
    );

    // R2in is LSB of T[4]+T[1] (equivalently XOR).
    check_r2in_sum_lsb: assert property (
        @(posedge CLK) R2in === (T[4] ^ T[1])
    );

    // R2out reflects T[3].
    check_r2out_map: assert property (
        @(posedge CLK) R2out === T[3]
    );

    // Add equals T[3] & Ins[0].
    check_add_map: assert property (
        @(posedge CLK) Add === (T[3] & Ins[0])
    );

    // Sub equals T[3] & Ins[1].
    check_sub_map: assert property (
        @(posedge CLK) Sub === (T[3] & Ins[1])
    );

    // Mul equals T[3] & Ins[2].
    check_mul_map: assert property (
        @(posedge CLK) Mul === (T[3] & Ins[2])
    );

    // Div equals T[3] & Ins[3].
    check_div_map: assert property (
        @(posedge CLK) Div === (T[3] & Ins[3])
    );

    // SelectY reflects T[3].
    check_selecty_map: assert property (
        @(posedge CLK) SelectY === T[3]
    );

    // Zin reflects T[3].
    check_zin_map: assert property (
        @(posedge CLK) Zin === T[3]
    );

    // Zout reflects T[4].
    check_zout_map: assert property (
        @(posedge CLK) Zout === T[4]
    );

    // Yin reflects T[2].
    check_yin_map: assert property (
        @(posedge CLK) Yin === T[2]
    );

    // End reflects T[5].
    check_end_map: assert property (
        @(posedge CLK) End === T[5]
    );
endmodule