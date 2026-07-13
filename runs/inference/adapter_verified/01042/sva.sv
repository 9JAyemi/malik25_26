module DFF_AR_sva (
    input logic CLK,
    input logic RST,
    input logic D,
    input logic Q,
    input logic QN
);

// Clock: CLK (posedge). Reset: RST active-low, asynchronous. Sequential DFF with Q=1'b0 and QN=1'b1 when RST is LOW.

    // When RST is LOW at a clock edge, Q must be 0 and QN must be 1.
    check_reset_forces_outputs: assert property (
        @(posedge CLK) !RST |-> (Q == 1'b0) && (QN == 1'b1)
    );

// On the first clock after RST rises, Q captures D and QN captures ~D.
    check_capture_after_reset_release: assert property (
        @(posedge CLK) disable iff (!RST) $rose(RST) |-> ##1 (Q == $past(D)) && (QN == ~$past(D))
    );

// With RST HIGH, Q and QN are complementary on every clock edge.
    check_complementary_outputs_when_active: assert property (
        @(posedge CLK) disable iff (!RST) 1'b1 |-> (QN == ~Q)
    );

// With RST HIGH, Q holds its value when D is equal to the previous Q.
    check_q_holds_when_d_matches_prev_q: assert property (
        @(posedge CLK) disable iff (!RST) (D == $past(Q)) |-> ##1 (Q == $past(Q))
    );

// With RST HIGH, QN holds its value when D is equal to the previous QN.
    check_qn_holds_when_d_matches_prev_qn: assert property (
        @(posedge CLK) disable iff (!RST) (D == $past(QN)) |-> ##1 (QN == $past(QN))
    );

// With RST HIGH, QN holds its value when D is equal to the previous Q.
    check_qn_holds_when_d_matches_prev_q: assert property (
        @(posedge CLK) disable iff (!RST) (D == $past(Q)) |-> ##1 (QN == $past(Q))
    );

// With RST HIGH, Q holds its value when D is equal to the previous QN.
    check_q_holds_when_d_matches_prev_qn: assert property (
        @(posedge CLK) disable iff (!RST) (D == $past(QN)) |-> ##1 (Q == $past(QN))
    );

endmodule
