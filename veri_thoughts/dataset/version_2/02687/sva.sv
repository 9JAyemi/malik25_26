module mux32_2_sva (
    input logic CLK,
    input logic [31:0] IN0,
    input logic [31:0] IN1,
    input logic CTRL,
    input logic [31:0] OUT1
);
    // When CTRL is 0, OUT1 mirrors IN0.
    check_select_ctrl0_vector: assert property (
        @(posedge CLK) (CTRL == 1'b0) |-> (OUT1 == IN0)
    );

    // When CTRL is 1, OUT1 mirrors IN1.
    check_select_ctrl1_vector: assert property (
        @(posedge CLK) (CTRL == 1'b1) |-> (OUT1 == IN1)
    );

    // Rising CTRL selects IN1 immediately.
    check_ctrl_rise_selects_IN1: assert property (
        @(posedge CLK) $rose(CTRL) |-> (OUT1 == IN1)
    );

    // Falling CTRL selects IN0 immediately.
    check_ctrl_fall_selects_IN0: assert property (
        @(posedge CLK) $fell(CTRL) |-> (OUT1 == IN0)
    );

    // OUT1 always equals either IN0 or IN1.
    check_output_is_one_of_inputs: assert property (
        @(posedge CLK) (OUT1 == IN0) || (OUT1 == IN1)
    );

    // Boolean mux identity: OUT1 == (CTRL ? IN1 : IN0).
    check_mux_boolean_equivalence: assert property (
        @(posedge CLK) OUT1 == (({32{CTRL}} & IN1) | ({32{~CTRL}} & IN0))
    );

    // If inputs are equal, OUT1 matches them.
    check_input_equality_passthrough: assert property (
        @(posedge CLK) (IN0 == IN1) |-> (OUT1 == IN0)
    );

    // With CTRL stable low and IN0 stable, OUT1 is stable.
    check_stability_when_ctrl0_in0_stable: assert property (
        @(posedge CLK) (CTRL == 1'b0) && $stable(CTRL) && $stable(IN0) |-> $stable(OUT1)
    );

    // With CTRL stable high and IN1 stable, OUT1 is stable.
    check_stability_when_ctrl1_in1_stable: assert property (
        @(posedge CLK) (CTRL == 1'b1) && $stable(CTRL) && $stable(IN1) |-> $stable(OUT1)
    );

    // If CTRL low and IN0 changes, OUT1 changes.
    check_out_changes_if_in0_changes_when_ctrl0: assert property (
        @(posedge CLK) (CTRL == 1'b0) && $stable(CTRL) && $changed(IN0) |-> $changed(OUT1)
    );

    // If CTRL high and IN1 changes, OUT1 changes.
    check_out_changes_if_in1_changes_when_ctrl1: assert property (
        @(posedge CLK) (CTRL == 1'b1) && $stable(CTRL) && $changed(IN1) |-> $changed(OUT1)
    );

    // With both inputs stable, any OUT1 change implies CTRL changed.
    check_ctrl_is_only_cause_of_change_when_inputs_stable: assert property (
        @(posedge CLK) $stable(IN0) && $stable(IN1) && $changed(OUT1) |-> $changed(CTRL)
    );
endmodule