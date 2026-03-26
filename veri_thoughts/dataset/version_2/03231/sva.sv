module d_ff_assertions (
    input logic Q,
    input logic Q_N,
    input logic CLK,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Q_N remains the complement of Q outside reset.
    check_qn_complement: assert property (
        @(posedge CLK) disable iff (VPB == 1'b0) Q_N == ~Q
    );

    // A low VPB on a clock edge clears Q by the next sampled cycle.
    check_reset_clears_q: assert property (
        @(posedge CLK) (VPB == 1'b0) |=> Q == 1'b0
    );

    // Outside reset, Q captures D on the following sampled cycle.
    check_q_captures_d: assert property (
        @(posedge CLK) disable iff (VPB == 1'b0) 1'b1 |=> Q == $past(D)
    );

    // A low VPB on a clock edge drives Q_N high by the next sampled cycle.
    check_reset_sets_qn_high: assert property (
        @(posedge CLK) (VPB == 1'b0) |=> Q_N == 1'b1
    );

endmodule