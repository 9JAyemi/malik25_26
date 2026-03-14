module stratixv_pll_dpa_output_sva #(
    parameter int output_clock_frequency = 0, // unused in RTL
    parameter int pll_vcoph_div = 1          // valid: 1|2|4
)(
    input  logic [0:0] pd,
    input  logic [7:0] phin,
    input  logic [7:0] phout
);
    // Local re-computation to match RTL truncation semantics (8-bit wrap)
    wire [7:0] sum8;
    assign sum8 = phin + 8'd40;

    wire [7:0] prod8;
    assign prod8 = sum8 * pll_vcoph_div;

    wire [7:0] affine8; // (phin * div) + (40 * div) mod 256
    assign affine8 = (phin * pll_vcoph_div) + (8'd40 * pll_vcoph_div);

    ///// Core functional equivalence /////
    // phout equals (phin + 40) * pll_vcoph_div modulo 256.
    check_phout_function: assert property (
        @(posedge phin[0]) (phout == prod8)
    );

    // Alternative algebraic form: phout == (phin*div + (40*div)) modulo 256.
    check_affine_form: assert property (
        @(posedge phin[0]) (phout == affine8)
    );

    ///// Specializations for pll_vcoph_div /////
    // For div=1, phout equals sum8 directly.
    generate
        if (pll_vcoph_div == 1) begin : g_div1
            // phout equals phin + 40 when div==1.
            check_div1_sum: assert property (
                @(posedge phin[0]) (phout == sum8)
            );
        end
        else if (pll_vcoph_div == 2) begin : g_div2
            // For div==2, multiplication is 8-bit left shift by 1.
            check_div2_shift: assert property (
                @(posedge phin[0]) (phout == {sum8[6:0], 1'b0})
            );
            // For div==2, LSB of phout must be 0.
            check_div2_lsb0: assert property (
                @(posedge phin[0]) (phout[0] == 1'b0)
            );
        end
        else if (pll_vcoph_div == 4) begin : g_div4
            // For div==4, multiplication is 8-bit left shift by 2.
            check_div4_shift: assert property (
                @(posedge phin[0]) (phout == {sum8[5:0], 2'b00})
            );
            // For div==4, lowest two bits of phout must be 0.
            check_div4_lsb00: assert property (
                @(posedge phin[0]) (phout[1:0] == 2'b00)
            );
        end
    endgenerate

endmodule