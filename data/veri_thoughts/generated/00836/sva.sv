module Cfu_sva (
  input logic               cmd_valid,
  input logic               cmd_ready,
  input logic [9:0]         cmd_payload_function_id,
  input logic [31:0]        cmd_payload_inputs_0,
  input logic [31:0]        cmd_payload_inputs_1,
  input logic               rsp_valid,
  input logic               rsp_ready,
  input logic [31:0]        rsp_payload_outputs_0,
  input logic               reset,
  input logic               clk
);
    // rsp_valid must mirror cmd_valid each cycle.
    check_rsp_valid_mirror: assert property (
        @(posedge clk) disable iff (reset) (rsp_valid == cmd_valid)
    );

    // cmd_ready must mirror rsp_ready each cycle.
    check_cmd_ready_mirror: assert property (
        @(posedge clk) disable iff (reset) (cmd_ready == rsp_ready)
    );

    // When select=0, output routes inputs_0.
    mux_select0_routes_in0: assert property (
        @(posedge clk) disable iff (reset) (!cmd_payload_function_id[0]) |-> (rsp_payload_outputs_0 == cmd_payload_inputs_0)
    );

    // When select=1, output routes inputs_1.
    mux_select1_routes_in1: assert property (
        @(posedge clk) disable iff (reset) (cmd_payload_function_id[0]) |-> (rsp_payload_outputs_0 == cmd_payload_inputs_1)
    );

    // Output equals the ternary mux of select and inputs.
    mux_function_equivalence: assert property (
        @(posedge clk) disable iff (reset) (rsp_payload_outputs_0 == (cmd_payload_function_id[0] ? cmd_payload_inputs_1 : cmd_payload_inputs_0))
    );

    // If select and both inputs are stable, the output remains stable.
    out_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (reset) ($stable(cmd_payload_function_id[0]) && $stable(cmd_payload_inputs_0) && $stable(cmd_payload_inputs_1)) |-> $stable(rsp_payload_outputs_0)
    );

    // Changes to function_id[9:1] alone cannot change the output.
    upper_id_bits_no_effect: assert property (
        @(posedge clk) disable iff (reset)
            ($stable(cmd_payload_function_id[0]) && $stable(cmd_payload_inputs_0) && $stable(cmd_payload_inputs_1) &&
             (cmd_payload_function_id[9:1] != $past(cmd_payload_function_id[9:1])))
            |-> $stable(rsp_payload_outputs_0)
    );

    // Rising edge on cmd_valid produces rising edge on rsp_valid.
    edge_rise_valid_mirror: assert property (
        @(posedge clk) disable iff (reset) $rose(cmd_valid) |-> $rose(rsp_valid)
    );

    // Falling edge on cmd_valid produces falling edge on rsp_valid.
    edge_fall_valid_mirror: assert property (
        @(posedge clk) disable iff (reset) $fell(cmd_valid) |-> $fell(rsp_valid)
    );

    // Rising edge on rsp_ready produces rising edge on cmd_ready.
    edge_rise_ready_mirror: assert property (
        @(posedge clk) disable iff (reset) $rose(rsp_ready) |-> $rose(cmd_ready)
    );

    // Falling edge on rsp_ready produces falling edge on cmd_ready.
    edge_fall_ready_mirror: assert property (
        @(posedge clk) disable iff (reset) $fell(rsp_ready) |-> $fell(cmd_ready)
    );
endmodule