module binary_dff_set_assertions (
    input logic D,
    input logic Q,
    input logic Q_N,
    input logic SET_B,
    input logic CLK,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // Q_N is always the inverse of Q.
    check_qn_complement: assert property (
        @(posedge CLK) (Q_N == ~Q)
    );

    // A high SET_B forces Q high on the next observed cycle.
    check_set_forces_q_high: assert property (
        @(posedge CLK) SET_B |=> (Q == 1'b1)
    );

    // A high SET_B forces Q_N low on the next observed cycle.
    check_set_forces_qn_low: assert property (
        @(posedge CLK) SET_B |=> (Q_N == 1'b0)
    );

    // A low SET_B captures D into Q.
    check_data_capture_q: assert property (
        @(posedge CLK) (!SET_B) |=> (Q == $past(D))
    );

    // A low SET_B captures the inverse of D into Q_N.
    check_data_capture_qn: assert property (
        @(posedge CLK) (!SET_B) |=> (Q_N == ~$past(D))
    );

endmodule