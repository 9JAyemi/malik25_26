// SVA for barrel_shifter
// Bindable, concise, full functional checking and coverage

module barrel_shifter_sva (
  input logic [3:0] data,
  input logic [1:0] shift,
  input logic [3:0] result
);

  default clocking cb @(*); endclocking

  function automatic logic [3:0] rotl1 (input logic [3:0] d);
    rotl1 = {d[2:0], d[3]};
  endfunction

  function automatic logic [3:0] rotr1 (input logic [3:0] d);
    rotr1 = {d[0], d[3:1]};
  endfunction

  // No X/Zs on inputs/outputs
  a_no_x_in:  assert property (!$isunknown({data,shift}));
  a_no_x_out: assert property (!$isunknown(result));

  // Combinational stability
  a_stable:   assert property ($stable({data,shift}) |-> $stable(result));

  // Result must be one of the 0/±1 rotations of data
  a_family:   assert property (result==data || result==rotl1(data) || result==rotr1(data));

  // Per-select functional checks (match current RTL behavior)
  a_s00: assert property ((shift==2'b00) |-> (result==data));
  a_s01: assert property ((shift==2'b01) |-> (result==rotl1(data)));
  a_s10: assert property ((shift==2'b10) |-> (result=={data[3],data[2:0]})); // equals data
  a_s11: assert property ((shift==2'b11) |-> (result==rotr1(data)));

  // Minimal but meaningful coverage
  c_s00: cover property (shift==2'b00);
  c_s01: cover property (shift==2'b01);
  c_s10: cover property (shift==2'b10);
  c_s11: cover property (shift==2'b11);

  c_rotl_obs: cover property (shift==2'b01 && result==rotl1(data));
  c_rotr_obs: cover property (shift==2'b11 && result==rotr1(data));
  c_hold_obs: cover property (shift inside {2'b00,2'b10} && result==data);

endmodule

// Bind into DUT
bind barrel_shifter barrel_shifter_sva sva_i (
  .data  (data),
  .shift (shift),
  .result(result)
);