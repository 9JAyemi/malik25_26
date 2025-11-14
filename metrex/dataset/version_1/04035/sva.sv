// SVA bind for control_unit
// Focused, high-quality checks + concise functional coverage

bind control_unit control_unit_sva u_control_unit_sva (.*);

module control_unit_sva (
  input logic              clk,
  input logic [1:0]        ctrl,
  input logic [3:0]        data_in,
  input logic              load,
  input logic [3:0]        data_out,
  input logic              valid,
  input logic [3:0]        reg_data
);

  default clocking cb @(posedge clk); endclocking

  // Guard for $past
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // X-prop hygiene on inputs when they are used
  assert property (disable iff (!past_valid)
    $past(!load) |-> !$isunknown($past(ctrl))
  ) else $error("ctrl has X/Z when used");

  // reg_data behavior
  assert property (disable iff (!past_valid)
    $past(load) |-> (reg_data == $past(data_in))
  ) else $error("reg_data did not capture data_in on load");

  assert property (disable iff (!past_valid)
    $past(!load) |-> (reg_data == $past(reg_data))
  ) else $error("reg_data changed without load");

  // Outputs must only update on non-load cycles
  assert property (disable iff (!past_valid)
    ((data_out != $past(data_out)) || (valid != $past(valid))) |-> $past(!load)
  ) else $error("Outputs changed on a load cycle");

  // Functional mapping on non-load cycles (use previous-cycle drivers)
  assert property (disable iff (!past_valid)
    $past(!load && (ctrl==2'b00)) |-> (data_out == $past(reg_data) && valid)
  ) else $error("ctrl==00: data_out/reg_data/valid mismatch");

  assert property (disable iff (!past_valid)
    $past(!load && (ctrl==2'b01)) |-> (data_out == ~$past(reg_data) && valid)
  ) else $error("ctrl==01: data_out/~reg_data/valid mismatch");

  assert property (disable iff (!past_valid)
    $past(!load && (ctrl==2'b10)) |-> (data_out == $past(data_in) && valid)
  ) else $error("ctrl==10: data_out/data_in/valid mismatch");

  assert property (disable iff (!past_valid)
    $past(!load && (ctrl==2'b11)) |-> (data_out == ~$past(data_in) && valid)
  ) else $error("ctrl==11: data_out/~data_in/valid mismatch");

  // Default branch behavior if ctrl is X/Z (4-state case default)
  assert property (disable iff (!past_valid)
    $past(!load && $isunknown($past(ctrl))) |-> (data_out==4'b0 && !valid)
  ) else $error("Default branch behavior mismatch");

  // After a non-load assignment, outputs must be known
  assert property (disable iff (!past_valid)
    $past(!load) |-> !$isunknown({data_out,valid})
  ) else $error("Outputs contain X/Z after assignment");

  // Power-up expectation from initial block
  assert property (@(posedge clk) $initstate |-> (reg_data==4'b0))
    else $error("reg_data not initialized to 0");

  // Concise functional coverage
  cover property (disable iff (!past_valid) $past(load) && (reg_data==$past(data_in)));
  cover property (disable iff (!past_valid) $past(!load && ctrl==2'b00) && (data_out==$past(reg_data)) && valid);
  cover property (disable iff (!past_valid) $past(!load && ctrl==2'b01) && (data_out==~$past(reg_data)) && valid);
  cover property (disable iff (!past_valid) $past(!load && ctrl==2'b10) && (data_out==$past(data_in)) && valid);
  cover property (disable iff (!past_valid) $past(!load && ctrl==2'b11) && (data_out==~$past(data_in)) && valid);

endmodule