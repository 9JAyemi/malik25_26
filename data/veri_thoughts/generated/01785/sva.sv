module top_module_sva (
    input logic [31:0] in,
    input logic [31:0] out_xor,
    input logic [31:0] out_and,
    input logic [15:0] lower_half,
    input logic [15:0] upper_half,
    input logic [15:0] xor_half,
    input logic [15:0] and_half
);
    // No explicit clock/reset in RTL; combinational design; sample on $global_clock.

    // Stage1: lower_half is in[15:0].
    check_stage1_lower_map: assert property (
        @(posedge $global_clock) lower_half == in[15:0]
    );

    // Stage1: upper_half is in[31:16].
    check_stage1_upper_map: assert property (
        @(posedge $global_clock) upper_half == in[31:16]
    );

    // Stage2: xor_half equals lower_half ^ upper_half.
    check_stage2_xor: assert property (
        @(posedge $global_clock) xor_half == (lower_half ^ upper_half)
    );

    // Stage2: and_half equals lower_half & upper_half.
    check_stage2_and: assert property (
        @(posedge $global_clock) and_half == (lower_half & upper_half)
    );

    // Stage3: out_xor[15:0] equals xor_half.
    check_stage3_out_xor_lsb: assert property (
        @(posedge $global_clock) out_xor[15:0] == xor_half
    );

    // Stage3: out_xor[31:16] are zero.
    check_stage3_out_xor_msb_zero: assert property (
        @(posedge $global_clock) out_xor[31:16] == 16'b0
    );

    // Stage3: out_and[15:0] equals and_half.
    check_stage3_out_and_lsb: assert property (
        @(posedge $global_clock) out_and[15:0] == and_half
    );

    // Stage3: out_and[31:16] are zero.
    check_stage3_out_and_msb_zero: assert property (
        @(posedge $global_clock) out_and[31:16] == 16'b0
    );

    // End-to-end: out_xor is zero-extended XOR of input halves.
    check_e2e_xor: assert property (
        @(posedge $global_clock) out_xor == {16'b0, (in[15:0] ^ in[31:16])}
    );

    // End-to-end: out_and is zero-extended AND of input halves.
    check_e2e_and: assert property (
        @(posedge $global_clock) out_and == {16'b0, (in[15:0] & in[31:16])}
    );
endmodule