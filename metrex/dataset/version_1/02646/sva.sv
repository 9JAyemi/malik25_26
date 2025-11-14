// SVA for shift_register_with_parallel_load
module shift_register_with_parallel_load_sva #(parameter W=512) (
  input clk,
  input load,
  input direction,
  input [W-1:0] data,
  input [W-1:0] q
);
  default clocking cb @(posedge clk); endclocking

  // Functional correctness
  ap_load:    assert property (load                   |=> q == $past(data));
  ap_shift_r: assert property (!load && direction     |=> q == {1'b0, $past(q[W-1:1])});
  ap_shift_l: assert property (!load && !direction    |=> q == {$past(q[W-2:0]), 1'b0});

  // Boundary bit insertion (redundant but pinpointing)
  ap_ins_msb0: assert property (!load && direction  |=> q[W-1] == 1'b0);
  ap_ins_lsb0: assert property (!load && !direction |=> q[0]   == 1'b0);

  // Inputs known when used
  ap_known_dir:  assert property (!load |-> !$isunknown(direction));
  ap_known_data: assert property ( load |-> !$isunknown(data));

  // Coverage
  cp_load:      cover property (load ##1 q == $past(data));
  cp_shift_r:   cover property (!load && direction);
  cp_shift_l:   cover property (!load && !direction);
  cp_r_boundary: cover property (!load && direction && $past(q[1]) ##1 q[0]);
  cp_l_boundary: cover property (!load && !direction && $past(q[W-2]) ##1 q[W-1]);
  cp_mix:       cover property (load ##1 (!load && !direction) ##1 (!load && direction));
endmodule

// Bind to DUT
bind shift_register_with_parallel_load
  shift_register_with_parallel_load_sva #(.W(512)) shift_register_with_parallel_load_sva_i (
    .clk(clk), .load(load), .direction(direction), .data(data), .q(q)
  );