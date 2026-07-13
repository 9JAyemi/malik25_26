module dff_preset_clear_sva (
    input logic D,
    input logic CLK,
    input logic PRE,
    input logic CLR,
    input logic Q,
    input logic Q_N
);

    // Q_N is always the complement of Q.
    check_outputs_complement: assert property (
        @(posedge CLK) Q_N === ~Q
    );

    // Clear forces Q low on the next clock, regardless of PRE.
    check_clear_forces_q_low: assert property (
        @(posedge CLK) CLR |=> (Q == 1'b0)
    );

    // Clear forces Q_N high on the next clock, regardless of PRE.
    check_clear_forces_qn_high: assert property (
        @(posedge CLK) CLR |=> (Q_N == 1'b1)
    );

    // Preset forces Q high when clear is not asserted.
    check_preset_forces_q_high: assert property (
        @(posedge CLK) (!CLR && PRE) |=> (Q == 1'b1)
    );

    // Preset forces Q_N low when clear is not asserted.
    check_preset_forces_qn_low: assert property (
        @(posedge CLK) (!CLR && PRE) |=> (Q_N == 1'b0)
    );

    // Without clear or preset, Q captures D on the next clock.
    check_data_capture_without_controls: assert property (
        @(posedge CLK) (!CLR && !PRE) |=> (Q == $past(D))
    );

    // Without clear or preset, Q_N matches the complement of captured D.
    check_qn_capture_without_controls: assert property (
        @(posedge CLK) (!CLR && !PRE) |=> (Q_N == ~$past(D))
    );

endmodule