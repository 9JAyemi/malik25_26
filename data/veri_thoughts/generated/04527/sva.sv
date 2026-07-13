module DFFAR_sva (
    input logic D,
    input logic CLK,
    input logic RST,
    input logic Q,
    input logic QN
);

    // When not in reset, QN must be the inverse of Q.
    check_qn_inverse_of_q: assert property (
        @(posedge CLK) disable iff (!RST) (QN == ~Q)
    );

    // A reset seen on a clock edge clears the outputs by the next sample.
    check_reset_clears_outputs: assert property (
        @(posedge CLK) (!RST) |=> ((Q == 1'b0) && (QN == 1'b1))
    );

    // With reset inactive, Q captures D on the next sampled clock.
    check_q_captures_d: assert property (
        @(posedge CLK) disable iff (!RST) 1'b1 |=> (Q == $past(D))
    );

    // With reset inactive, QN reflects the inverse of the captured D.
    check_qn_captures_inverted_d: assert property (
        @(posedge CLK) disable iff (!RST) 1'b1 |=> (QN == ~$past(D))
    );

endmodule