module dff_async_reset_sva (
    input logic clk,
    input logic rst,
    input logic d,
    input logic q,
    input logic q_n
);

    // A clock seen with reset active drives reset values by the next sample.
    check_reset_drives_outputs: assert property (
        @(posedge clk) !rst |=> ((q == 1'b0) && (q_n == 1'b1))
    );

    // q captures d on the next active clock.
    check_q_captures_d: assert property (
        @(posedge clk) disable iff (!rst) 1'b1 |=> (q == $past(d))
    );

    // q_n captures the inverse of d on the next active clock.
    check_qn_captures_inverted_d: assert property (
        @(posedge clk) disable iff (!rst) 1'b1 |=> (q_n == ~$past(d))
    );

    // After any clock edge, q and q_n are complementary by the next sample.
    check_outputs_are_complements: assert property (
        @(posedge clk) 1'b1 |=> (q_n == ~q)
    );

    // A sampled high d produces q high and q_n low on the next active clock.
    check_d_high_response: assert property (
        @(posedge clk) disable iff (!rst) d |=> ((q == 1'b1) && (q_n == 1'b0))
    );

    // A sampled low d produces q low and q_n high on the next active clock.
    check_d_low_response: assert property (
        @(posedge clk) disable iff (!rst) !d |=> ((q == 1'b0) && (q_n == 1'b1))
    );

endmodule