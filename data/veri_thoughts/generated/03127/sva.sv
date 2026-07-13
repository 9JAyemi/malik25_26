module decalper_eb_ot_sdeen_pot_pi_dehcac_xnilix_mult_gen_v12_0_12_sva (
    input logic CLK,
    input logic [16:0] A,
    input logic [15:0] B,
    input logic CE,
    input logic SCLR,
    input logic [1:0] ZERO_DETECT,
    input logic [32:0] P,
    input logic [63:0] PCASC
);

    // P is always the combinational product of A and B.
    check_product_matches_inputs: assert property (
        @(posedge CLK) disable iff (1'b0)
        P == (A * B)
    );

    // ZERO_DETECT reflects whether P is zero.
    check_zero_detect_matches_product_zero: assert property (
        @(posedge CLK) disable iff (1'b0)
        ZERO_DETECT == ((P == 33'd0) ? 2'b11 : 2'b00)
    );

    // PCASC is tied to zero.
    check_pcasc_constant_zero: assert property (
        @(posedge CLK) disable iff (1'b0)
        PCASC == 64'h0
    );

    // ZERO_DETECT only uses the implemented encodings.
    check_zero_detect_legal_values: assert property (
        @(posedge CLK) disable iff (1'b0)
        (ZERO_DETECT == 2'b00) || (ZERO_DETECT == 2'b11)
    );

    // A equal to zero forces a zero product and asserted zero detect.
    check_a_zero_forces_zero_outputs: assert property (
        @(posedge CLK) disable iff (1'b0)
        (A == 17'd0) |-> (P == 33'd0 && ZERO_DETECT == 2'b11)
    );

    // B equal to zero forces a zero product and asserted zero detect.
    check_b_zero_forces_zero_outputs: assert property (
        @(posedge CLK) disable iff (1'b0)
        (B == 16'd0) |-> (P == 33'd0 && ZERO_DETECT == 2'b11)
    );

    // Nonzero operands produce a nonzero full-width product.
    check_nonzero_operands_produce_nonzero_product: assert property (
        @(posedge CLK) disable iff (1'b0)
        ((A != 17'd0) && (B != 16'd0)) |-> (P != 33'd0 && ZERO_DETECT == 2'b00)
    );

    // Stable operands keep all outputs stable.
    check_outputs_stable_when_operands_stable: assert property (
        @(posedge CLK) disable iff (1'b0)
        ($stable(A) && $stable(B)) |-> ($stable(P) && $stable(ZERO_DETECT) && $stable(PCASC))
    );

    // CE and SCLR do not affect outputs when operands are unchanged.
    check_controls_do_not_affect_outputs: assert property (
        @(posedge CLK) disable iff (1'b0)
        ($stable(A) && $stable(B) && ($changed(CE) || $changed(SCLR))) |-> ($stable(P) && $stable(ZERO_DETECT) && $stable(PCASC))
    );

endmodule