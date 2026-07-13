module phase_accumulator_sva #
(
    parameter WIDTH = 32,
    parameter [WIDTH-1:0] INITIAL_PHASE = 0,
    parameter [WIDTH-1:0] INITIAL_PHASE_STEP = 0
)
(
    input logic             clk,
    input logic             rst,

    input logic [WIDTH-1:0] input_phase_tdata,
    input logic             input_phase_tvalid,
    input logic             input_phase_tready,

    input logic [WIDTH-1:0] input_phase_step_tdata,
    input logic             input_phase_step_tvalid,
    input logic             input_phase_step_tready,

    input logic [WIDTH-1:0] output_phase_tdata,
    input logic             output_phase_tvalid,
    input logic             output_phase_tready
);

    // input_phase_tready is a direct mirror of output_phase_tready.
    check_input_phase_ready_mirrors_output_ready: assert property (
        @(posedge clk) disable iff (rst)
        (input_phase_tready == output_phase_tready)
    );

    // input_phase_step_tready is permanently asserted.
    check_input_phase_step_ready_constant: assert property (
        @(posedge clk) disable iff (rst)
        (input_phase_step_tready == 1'b1)
    );

    // output_phase_tvalid is permanently asserted.
    check_output_phase_valid_constant: assert property (
        @(posedge clk) disable iff (rst)
        (output_phase_tvalid == 1'b1)
    );

    // The constant handshake outputs also hold during reset.
    check_reset_constant_outputs: assert property (
        @(posedge clk)
        rst |-> ((input_phase_tready == output_phase_tready) &&
                 (input_phase_step_tready == 1'b1) &&
                 (output_phase_tvalid == 1'b1))
    );

    // Reset reloads the phase output to INITIAL_PHASE.
    check_reset_loads_initial_phase: assert property (
        @(posedge clk)
        rst |=> (output_phase_tdata == INITIAL_PHASE)
    );

    // A valid input phase handshake loads the next output phase.
    check_phase_load_on_input_handshake: assert property (
        @(posedge clk) disable iff (rst)
        (input_phase_tready && input_phase_tvalid)
        |=> (output_phase_tdata == $past(input_phase_tdata))
    );

    // Without a phase load or ready advance, the phase output holds.
    check_phase_holds_without_load_or_advance: assert property (
        @(posedge clk) disable iff (rst)
        (!(input_phase_tready && input_phase_tvalid) && !output_phase_tready)
        |=> (output_phase_tdata == $past(output_phase_tdata))
    );

    // After reset releases, the first eligible advance uses INITIAL_PHASE_STEP.
    check_reset_step_used_on_first_increment: assert property (
        @(posedge clk)
        rst ##1 (!rst && !(input_phase_tready && input_phase_tvalid) && output_phase_tready)
        |=> (output_phase_tdata == $past(output_phase_tdata) + INITIAL_PHASE_STEP)
    );

    // A written phase step is used by the next eligible advance.
    check_updated_step_used_on_next_increment: assert property (
        @(posedge clk) disable iff (rst)
        input_phase_step_tvalid ##1 (!(input_phase_tready && input_phase_tvalid) && output_phase_tready)
        |=> (output_phase_tdata == $past(output_phase_tdata) + $past(input_phase_step_tdata, 2))
    );

endmodule