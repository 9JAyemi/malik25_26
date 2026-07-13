module QPSK_Demodulator_Baseband_assertions (
    input logic clk,
    input logic signed [15:0] in0_re,
    input logic signed [15:0] in0_im,
    input logic [1:0] out0
);

    // No clock or reset exists in the RTL; sample combinational behavior on clk.

    // Positive in-phase and positive quadrature map to 00.
    check_pospos_symbol: assert property (
        @(posedge clk)
        (in0_re > 16'sd0 && in0_im > 16'sd0) |-> (out0 == 2'b00)
    );

    // Positive in-phase and zero quadrature map to 00.
    check_poszero_symbol: assert property (
        @(posedge clk)
        (in0_re > 16'sd0 && in0_im == 16'sd0) |-> (out0 == 2'b00)
    );

    // Positive in-phase and negative quadrature map to 10.
    check_posneg_symbol: assert property (
        @(posedge clk)
        (in0_re > 16'sd0 && in0_im < 16'sd0) |-> (out0 == 2'b10)
    );

    // Zero in-phase and positive quadrature map to 01.
    check_zeropos_symbol: assert property (
        @(posedge clk)
        (in0_re == 16'sd0 && in0_im > 16'sd0) |-> (out0 == 2'b01)
    );

    // Zero in-phase and zero quadrature map to 00.
    check_zerozero_symbol: assert property (
        @(posedge clk)
        (in0_re == 16'sd0 && in0_im == 16'sd0) |-> (out0 == 2'b00)
    );

    // Zero in-phase and negative quadrature map to 10.
    check_zeroneg_symbol: assert property (
        @(posedge clk)
        (in0_re == 16'sd0 && in0_im < 16'sd0) |-> (out0 == 2'b10)
    );

    // Negative in-phase and positive quadrature map to 01.
    check_negpos_symbol: assert property (
        @(posedge clk)
        (in0_re < 16'sd0 && in0_im > 16'sd0) |-> (out0 == 2'b01)
    );

    // Negative in-phase and zero quadrature map to 11.
    check_negzero_symbol: assert property (
        @(posedge clk)
        (in0_re < 16'sd0 && in0_im == 16'sd0) |-> (out0 == 2'b11)
    );

    // Negative in-phase and negative quadrature map to 11.
    check_negneg_symbol: assert property (
        @(posedge clk)
        (in0_re < 16'sd0 && in0_im < 16'sd0) |-> (out0 == 2'b11)
    );

endmodule