module top_module_sva (
    input  logic        clk,
    input  logic [15:0] D,
    input  logic [3:0]  shift_ctrl,
    input  logic [31:0] a,
    input  logic [31:0] b,
    input  logic [3:0]  alu_ctrl,
    input  logic [31:0] result,
    input  logic [15:0] shifted_D,
    input  logic [31:0] alu_result,
    input  logic [31:0] or_result
);

    function automatic logic [15:0] expected_shift (
        input logic [15:0] d_i,
        input logic [3:0]  shift_i
    );
        case (shift_i)
            4'b0000: expected_shift = d_i << 1;
            4'b0001: expected_shift = d_i << 2;
            4'b0010: expected_shift = d_i << 4;
            4'b0011: expected_shift = d_i << 8;
            4'b0100: expected_shift = d_i >> 1;
            4'b0101: expected_shift = d_i >> 2;
            4'b0110: expected_shift = d_i >> 4;
            4'b0111: expected_shift = d_i >> 8;
            default: expected_shift = d_i;
        endcase
    endfunction

    function automatic logic [31:0] expected_alu (
        input logic [31:0] a_i,
        input logic [31:0] b_i,
        input logic [3:0]  ctrl_i
    );
        case (ctrl_i)
            4'b0000: expected_alu = a_i + b_i;
            4'b0001: expected_alu = a_i - b_i;
            4'b0010: expected_alu = a_i & b_i;
            4'b0011: expected_alu = a_i | b_i;
            4'b0100: expected_alu = a_i ^ b_i;
            default: expected_alu = a_i;
        endcase
    endfunction

    // Barrel shifter output matches the shift control decoding.
    check_shifted_d_matches_spec: assert property (
        @(posedge clk) shifted_D == expected_shift(D, shift_ctrl)
    );

    // Barrel shifter default case passes D through unchanged.
    check_shift_default_passthrough: assert property (
        @(posedge clk) shift_ctrl[3] |-> shifted_D == D
    );

    // ALU output matches the control decoding.
    check_alu_result_matches_spec: assert property (
        @(posedge clk) alu_result == expected_alu(a, b, alu_ctrl)
    );

    // ALU default case passes a through unchanged.
    check_alu_default_passthrough: assert property (
        @(posedge clk) (alu_ctrl > 4'b0100) |-> alu_result == a
    );

    // OR stage combines zero-extended shifted_D with alu_result.
    check_or_result_composition: assert property (
        @(posedge clk) or_result == ({16'b0, shifted_D} | alu_result)
    );

    // Top-level result follows the OR stage output.
    check_result_tracks_or_result: assert property (
        @(posedge clk) result == or_result
    );

    // Upper result bits come only from the ALU path.
    check_result_upper_half_matches_alu: assert property (
        @(posedge clk) result[31:16] == alu_result[31:16]
    );

    // Lower result bits preserve all ones from the shifted data.
    check_result_contains_shift_ones: assert property (
        @(posedge clk) (result[15:0] & shifted_D) == shifted_D
    );

    // Result preserves all ones from the ALU output.
    check_result_contains_alu_ones: assert property (
        @(posedge clk) (result & alu_result) == alu_result
    );

    // Top-level result matches the full end-to-end combinational spec.
    check_result_matches_full_spec: assert property (
        @(posedge clk) result == ({16'b0, expected_shift(D, shift_ctrl)} | expected_alu(a, b, alu_ctrl))
    );

endmodule