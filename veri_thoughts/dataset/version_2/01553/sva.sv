module mult16_16_sva (
    input logic CLK,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic CE,
    input logic SCLR,
    input logic [1:0] ZERO_DETECT,
    input logic [7:0] P,
    input logic [47:0] PCASC
);
    // P equals the low 8 bits of A*B.
    check_p_low8_of_product: assert property (
        @(posedge CLK) P == (A * B)[7:0]
    );

    // PCASC equals {16'h0, A*B}.
    check_pcasc_matches_product: assert property (
        @(posedge CLK) PCASC == {16'h0000, (A * B)}
    );

    // Upper 16 bits of PCASC are zero.
    check_pcasc_upper16_zero: assert property (
        @(posedge CLK) PCASC[47:32] == 16'h0000
    );

    // P equals the low byte of PCASC.
    check_p_equals_pcasc_low8: assert property (
        @(posedge CLK) P == PCASC[7:0]
    );

    // ZERO_DETECT is 2'b11 when product is zero.
    check_zero_detect_zero_case: assert property (
        @(posedge CLK) ((A * B) == 32'd0) |-> (ZERO_DETECT == 2'b11)
    );

    // ZERO_DETECT is 2'b10 when product is nonzero and fits in 8 bits.
    check_zero_detect_low8_case: assert property (
        @(posedge CLK) (((A * B) != 32'd0) && (((A * B)[31:8]) == 24'd0)) |-> (ZERO_DETECT == 2'b10)
    );

    // ZERO_DETECT is 2'b01 when product exceeds 8 bits.
    check_zero_detect_high_case: assert property (
        @(posedge CLK) (((A * B)[31:8]) != 24'd0) |-> (ZERO_DETECT == 2'b01)
    );

    // ZERO_DETECT never takes value 2'b00.
    check_zero_detect_no_00: assert property (
        @(posedge CLK) ZERO_DETECT != 2'b00
    );

    // ZERO_DETECT[1] indicates product fits in 8 bits.
    check_zero_detect_bit1: assert property (
        @(posedge CLK) ZERO_DETECT[1] == (((A * B)[31:8]) == 24'd0)
    );

    // ZERO_DETECT[0] is 1 if product is zero or exceeds 8 bits.
    check_zero_detect_bit0: assert property (
        @(posedge CLK) ZERO_DETECT[0] == ( ((A * B) == 32'd0) || (((A * B)[31:8]) != 24'd0) )
    );

    // Outputs remain stable when A and B are stable.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(B)) |-> $stable({P, PCASC, ZERO_DETECT})
    );

    // Zero operand drives zero outputs and ZERO_DETECT==2'b11.
    check_zero_operand_zero_outputs: assert property (
        @(posedge CLK) ((A == 16'd0) || (B == 16'd0)) |-> ((P == 8'd0) && (PCASC == 48'd0) && (ZERO_DETECT == 2'b11))
    );
endmodule