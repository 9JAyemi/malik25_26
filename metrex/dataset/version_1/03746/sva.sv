// SVA for Cfu
module Cfu_sva (
  input  logic               cmd_valid,
  input  logic               cmd_ready,
  input  logic [9:0]         cmd_payload_function_id,
  input  logic [31:0]        cmd_payload_inputs_0,
  input  logic [31:0]        cmd_payload_inputs_1,
  input  logic               rsp_valid,
  input  logic               rsp_ready,
  input  logic [31:0]        rsp_payload_outputs_0,
  input  logic               reset,
  input  logic               clk
);

  default clocking @(posedge clk); endclocking
  default disable iff (reset);

  // Mirror checks
  a_rsp_valid_mirror: assert property (rsp_valid == cmd_valid);
  a_cmd_ready_mirror: assert property (cmd_ready == rsp_ready);

  // Functional mux correctness
  a_mux_eq: assert property (
    rsp_payload_outputs_0 == (cmd_payload_function_id[0] ? cmd_payload_inputs_1
                                                         : cmd_payload_inputs_0)
  );

  // Handshake equivalence across passthrough
  a_hs_equiv: assert property (
    (cmd_valid && rsp_ready) == (rsp_valid && cmd_ready)
  );

  // Coverage
  c_hs_sel0:            cover property (cmd_valid && rsp_ready && !cmd_payload_function_id[0]);
  c_hs_sel1:            cover property (cmd_valid && rsp_ready &&  cmd_payload_function_id[0]);
  c_stall_then_accept:  cover property (cmd_valid && !rsp_ready ##1 cmd_valid && rsp_ready);
  c_sink_ready_idle:    cover property (!cmd_valid && rsp_ready);

endmodule

bind Cfu Cfu_sva cfu_sva_i (.*);