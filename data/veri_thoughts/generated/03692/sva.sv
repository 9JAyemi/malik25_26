module pcx_buf_p0_even_sva (
    input logic clk,

    input logic arbpc0_pcxdp_grant_pa,
    input logic arbpc0_pcxdp_q0_hold_pa_l,
    input logic arbpc0_pcxdp_qsel0_pa,
    input logic arbpc0_pcxdp_qsel1_pa_l,
    input logic arbpc0_pcxdp_shift_px,

    input logic arbpc2_pcxdp_grant_pa,
    input logic arbpc2_pcxdp_q0_hold_pa_l,
    input logic arbpc2_pcxdp_qsel0_pa,
    input logic arbpc2_pcxdp_qsel1_pa_l,
    input logic arbpc2_pcxdp_shift_px,

    input logic scache0_pcx_stall_bufp0even_pq,

    input logic arbpc0_pcxdp_grant_bufp1_pa_l,
    input logic arbpc0_pcxdp_q0_hold_bufp1_pa,
    input logic arbpc0_pcxdp_qsel0_bufp1_pa_l,
    input logic arbpc0_pcxdp_qsel1_bufp1_pa,
    input logic arbpc0_pcxdp_shift_bufp1_px_l,

    input logic arbpc2_pcxdp_grant_bufp1_pa_l,
    input logic arbpc2_pcxdp_q0_hold_bufp1_pa,
    input logic arbpc2_pcxdp_qsel0_bufp1_pa_l,
    input logic arbpc2_pcxdp_qsel1_bufp1_pa,
    input logic arbpc2_pcxdp_shift_bufp1_px_l,

    input logic scache0_pcx_stall_pq
);

    // arbpc0 grant output is the inverse of the active-low bufp1 grant input.
    check_arbpc0_grant_inversion: assert property (
        @(posedge clk) arbpc0_pcxdp_grant_pa == ~arbpc0_pcxdp_grant_bufp1_pa_l
    );

    // arbpc0 q0 hold output is the inverse of the bufp1 q0 hold input.
    check_arbpc0_q0_hold_inversion: assert property (
        @(posedge clk) arbpc0_pcxdp_q0_hold_pa_l == ~arbpc0_pcxdp_q0_hold_bufp1_pa
    );

    // arbpc0 qsel0 output is the inverse of the active-low bufp1 qsel0 input.
    check_arbpc0_qsel0_inversion: assert property (
        @(posedge clk) arbpc0_pcxdp_qsel0_pa == ~arbpc0_pcxdp_qsel0_bufp1_pa_l
    );

    // arbpc0 qsel1 output is the inverse of the bufp1 qsel1 input.
    check_arbpc0_qsel1_inversion: assert property (
        @(posedge clk) arbpc0_pcxdp_qsel1_pa_l == ~arbpc0_pcxdp_qsel1_bufp1_pa
    );

    // arbpc0 shift output is the inverse of the active-low bufp1 shift input.
    check_arbpc0_shift_inversion: assert property (
        @(posedge clk) arbpc0_pcxdp_shift_px == ~arbpc0_pcxdp_shift_bufp1_px_l
    );

    // arbpc2 grant output is the inverse of the active-low bufp1 grant input.
    check_arbpc2_grant_inversion: assert property (
        @(posedge clk) arbpc2_pcxdp_grant_pa == ~arbpc2_pcxdp_grant_bufp1_pa_l
    );

    // arbpc2 q0 hold output is the inverse of the bufp1 q0 hold input.
    check_arbpc2_q0_hold_inversion: assert property (
        @(posedge clk) arbpc2_pcxdp_q0_hold_pa_l == ~arbpc2_pcxdp_q0_hold_bufp1_pa
    );

    // arbpc2 qsel0 output is the inverse of the active-low bufp1 qsel0 input.
    check_arbpc2_qsel0_inversion: assert property (
        @(posedge clk) arbpc2_pcxdp_qsel0_pa == ~arbpc2_pcxdp_qsel0_bufp1_pa_l
    );

    // arbpc2 qsel1 output is the inverse of the bufp1 qsel1 input.
    check_arbpc2_qsel1_inversion: assert property (
        @(posedge clk) arbpc2_pcxdp_qsel1_pa_l == ~arbpc2_pcxdp_qsel1_bufp1_pa
    );

    // arbpc2 shift output is the inverse of the active-low bufp1 shift input.
    check_arbpc2_shift_inversion: assert property (
        @(posedge clk) arbpc2_pcxdp_shift_px == ~arbpc2_pcxdp_shift_bufp1_px_l
    );

    // The stall output is a direct pass-through of the stall input.
    check_stall_passthrough: assert property (
        @(posedge clk) scache0_pcx_stall_bufp0even_pq == scache0_pcx_stall_pq
    );

endmodule