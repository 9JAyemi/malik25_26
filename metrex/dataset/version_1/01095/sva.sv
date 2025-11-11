// SVA for ChooseModule
module ChooseModule_sva (
  input logic io_valid_0,
  input logic io_ready,
  input logic io_chosen
);
  // Sample any change on relevant signals
  default clocking cb @(io_ready or io_valid_0 or io_chosen); endclocking

  // No X on output when inputs are known
  a_known: assert property ( !$isunknown({io_ready, io_valid_0}) |-> !$isunknown(io_chosen) );

  // Spec checks
  a_ready0_forces_one: assert property ( !io_ready |-> (io_chosen == 1'b1) );
  a_func_when_known:   assert property ( !$isunknown({io_ready, io_valid_0})
                                         |-> (io_chosen == (~io_ready | ~io_valid_0)) );

  // Functional coverage
  c_ready0:      cover property ( !io_ready && io_chosen );
  c_ready1_v0:   cover property ( io_ready && !io_valid_0 && io_chosen );
  c_ready1_v1:   cover property ( io_ready &&  io_valid_0 && !io_chosen );
  c_chosen_rise: cover property ( $rose(io_chosen) );
  c_chosen_fall: cover property ( $fell(io_chosen) );
endmodule

// Bind into the DUT
bind ChooseModule ChooseModule_sva sva_i (
  .io_valid_0(io_valid_0),
  .io_ready  (io_ready),
  .io_chosen (io_chosen)
);