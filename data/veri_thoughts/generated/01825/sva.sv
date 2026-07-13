module dff_srst_as_set_sva (
    input logic CLK,
    input logic D,
    input logic S,
    input logic R,
    input logic Q
);
    // When R=1, next Q captures D.
    check_r_data_capture: assert property (
        @(posedge CLK) R |=> (Q == $past(D))
    );

    // When R=0 and S=1, next Q is set to 1.
    check_set_when_r0_s1: assert property (
        @(posedge CLK) (!R && S) |=> (Q == 1'b1)
    );

    // When R=0 and S=0, Q holds its value.
    check_hold_when_r0_s0: assert property (
        @(posedge CLK) (!R && !S) |=> (Q == $past(Q))
    );

    // R overrides S: if R=1 and D=0, next Q is 0.
    check_r_overrides_s_d0: assert property (
        @(posedge CLK) (R && S && (D == 1'b0)) |=> (Q == 1'b0)
    );

    // R overrides S: if R=1 and D=1, next Q is 1.
    check_r_overrides_s_d1: assert property (
        @(posedge CLK) (R && S && (D == 1'b1)) |=> (Q == 1'b1)
    );

    // A falling edge on Q can only occur if prior R was 1.
    check_q_fall_requires_r: assert property (
        @(posedge CLK) $fell(Q) |-> $past(R)
    );

    // A falling edge on Q implies prior R=1 and prior D=0.
    check_q_fall_requires_r_and_d0: assert property (
        @(posedge CLK) $fell(Q) |-> ($past(R) && ($past(D) == 1'b0))
    );

    // A rising edge on Q implies prior (R=1 and D=1) or prior (R=0 and S=1).
    check_q_rise_requires_r_or_s: assert property (
        @(posedge CLK) $rose(Q) |-> ( ($past(R) && $past(D)) || ($past(!R && S)) )
    );

    // Any change on Q requires prior R=1 or prior (R=0 and S=1).
    check_q_change_requires_enable: assert property (
        @(posedge CLK) $changed(Q) |-> ( $past(R) || $past(!R && S) )
    );

    // If R=1 and D equals current Q, Q remains unchanged next cycle.
    check_no_change_if_r1_and_d_eq_q: assert property (
        @(posedge CLK) (R && (D == Q)) |=> (Q == $past(Q))
    );
endmodule