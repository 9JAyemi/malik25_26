module DFF_AR_sva (
    input logic CLK,
    input logic RST,
    input logic D,
    input logic Q,
    input logic QN
);

    // Active-low reset forces Q low and QN high.
    check_reset_state: assert property (
        @(posedge CLK) !RST |-> (Q == 1'b0 && QN == 1'b1)
    );

    // Q captures D on the next clock when reset is inactive.
    check_q_captures_d: assert property (
        @(posedge CLK) disable iff (!RST) 1'b1 |=> (Q == $past(D))
    );

    // QN captures the inverse of D on the next clock when reset is inactive.
    check_qn_captures_not_d: assert property (
        @(posedge CLK) disable iff (!RST) 1'b1 |=> (QN == ~$past(D))
    );

    // Q and QN remain complementary when reset is inactive.
    check_outputs_complementary: assert property (
        @(posedge CLK) disable iff (!RST) 1'b1 |-> (QN == ~Q)
    );

endmodule