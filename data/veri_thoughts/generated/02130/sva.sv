module dff_with_set_clear_preset_sva (
    input logic CLK,
    input logic D,
    input logic SET,
    input logic CLR,
    input logic PRE,
    input logic Q,
    input logic Q_N
);
    // Q_N is always the complement of Q.
    check_qn_complement: assert property (
        @(posedge CLK) Q_N == ~Q
    );

    // If SET was 1 in the previous cycle, Q must be 1 now (highest priority).
    check_set_priority: assert property (
        @(posedge CLK) $past(SET) |-> (Q == 1'b1)
    );

    // If CLR was 1 and SET was 0 in the previous cycle, Q must be 0.
    check_clr_priority: assert property (
        @(posedge CLK) (!$past(SET) && $past(CLR)) |-> (Q == 1'b0)
    );

    // If PRE was 1 and SET/CLR were 0 in the previous cycle, Q must be 1.
    check_pre_priority: assert property (
        @(posedge CLK) (!$past(SET) && !$past(CLR) && $past(PRE)) |-> (Q == 1'b1)
    );

    // If no controls were 1 in the previous cycle, Q captures D from the previous cycle.
    check_data_capture_no_controls: assert property (
        @(posedge CLK) (!$past(SET) && !$past(CLR) && !$past(PRE)) |-> (Q == $past(D))
    );

    // SET overrides CLR when both were 1 in the previous cycle.
    check_set_overrides_clr: assert property (
        @(posedge CLK) ($past(SET) && $past(CLR)) |-> (Q == 1'b1)
    );

    // SET overrides PRE when both were 1 in the previous cycle.
    check_set_overrides_pre: assert property (
        @(posedge CLK) ($past(SET) && $past(PRE)) |-> (Q == 1'b1)
    );

    // CLR overrides PRE when SET was 0 and both CLR and PRE were 1 in the previous cycle.
    check_clr_overrides_pre: assert property (
        @(posedge CLK) (!$past(SET) && $past(CLR) && $past(PRE)) |-> (Q == 1'b0)
    );

    // If CLR was 1 and SET was 0 in the previous cycle, Q_N must be 1 now.
    check_qn_on_clr: assert property (
        @(posedge CLK) (!$past(SET) && $past(CLR)) |-> (Q_N == 1'b1)
    );

    // If SET was 1 in the previous cycle, Q_N must be 0 now.
    check_qn_on_set: assert property (
        @(posedge CLK) $past(SET) |-> (Q_N == 1'b0)
    );
endmodule