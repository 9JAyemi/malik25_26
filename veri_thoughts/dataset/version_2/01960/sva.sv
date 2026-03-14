module cpx_fpbuf_p0_sva (
    input  logic        clk,
    input  logic        reset_n,
    input  logic [7:0]  fp_cpx_req_bufpt_cq_l,
    input  logic [7:0]  fp_cpx_req_bufp0_cq
);
    // Output is bitwise inversion of input each cycle.
    check_bitwise_inversion: assert property (
        @(posedge clk) disable iff (!reset_n)
        fp_cpx_req_bufp0_cq == ~fp_cpx_req_bufpt_cq_l
    );

    // Out XOR In is all ones (complement relation).
    check_xor_all_ones: assert property (
        @(posedge clk) disable iff (!reset_n)
        (fp_cpx_req_bufp0_cq ^ fp_cpx_req_bufpt_cq_l) == 8'hFF
    );

    // Out OR In is all ones (no bit can be 0 on both).
    check_or_all_ones: assert property (
        @(posedge clk) disable iff (!reset_n)
        (fp_cpx_req_bufp0_cq | fp_cpx_req_bufpt_cq_l) == 8'hFF
    );

    // Out AND In is all zeros (no bit can be 1 on both).
    check_and_all_zero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (fp_cpx_req_bufp0_cq & fp_cpx_req_bufpt_cq_l) == 8'h00
    );

    // The inversion relation also holds for the previous cycle.
    check_past_inversion: assert property (
        @(posedge clk) disable iff (!reset_n)
        $past(fp_cpx_req_bufp0_cq) == ~ $past(fp_cpx_req_bufpt_cq_l)
    );

    // If input is unchanged cycle-to-cycle, output is unchanged too.
    check_hold_when_input_holds: assert property (
        @(posedge clk) disable iff (!reset_n)
        (fp_cpx_req_bufpt_cq_l == $past(fp_cpx_req_bufpt_cq_l)) |-> (fp_cpx_req_bufp0_cq == $past(fp_cpx_req_bufp0_cq))
    );

    // Bits that rise on output equal bits that fall on input.
    check_rising_out_equals_falling_in: assert property (
        @(posedge clk) disable iff (!reset_n)
        ((~$past(fp_cpx_req_bufp0_cq)) & fp_cpx_req_bufp0_cq) == (($past(fp_cpx_req_bufpt_cq_l)) & ~fp_cpx_req_bufpt_cq_l)
    );

    // Bits that fall on output equal bits that rise on input.
    check_falling_out_equals_rising_in: assert property (
        @(posedge clk) disable iff (!reset_n)
        (($past(fp_cpx_req_bufp0_cq)) & ~fp_cpx_req_bufp0_cq) == ((~$past(fp_cpx_req_bufpt_cq_l)) & fp_cpx_req_bufpt_cq_l)
    );

    // The set of toggling bits matches between input and output.
    check_toggle_set_matches: assert property (
        @(posedge clk) disable iff (!reset_n)
        (fp_cpx_req_bufpt_cq_l ^ $past(fp_cpx_req_bufpt_cq_l)) == (fp_cpx_req_bufp0_cq ^ $past(fp_cpx_req_bufp0_cq))
    );
endmodule