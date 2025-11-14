// SVA for ram_controller_ex_lfsr8
module ram_controller_ex_lfsr8_sva #(parameter int seed = 32)
(
  input  logic        clk,
  input  logic        reset_n,
  input  logic        enable,
  input  logic        pause,
  input  logic        load,
  input  logic [7:0]  data,
  input  logic [7:0]  ldata,
  input  logic [7:0]  lfsr_data
);

  default clocking cb @(posedge clk); endclocking

  // Output mirrors internal state
  a_data_mirrors_state: assert property (data == lfsr_data);

  // No X/Z on key signals once reset_n is known
  a_no_x_ctrl: assert property (!$isunknown(reset_n) |-> !$isunknown({enable,pause,load,ldata,data,lfsr_data}));

  // Asynchronous reset seeds the LFSR whenever sampled low
  a_async_reset_seeds: assert property (!reset_n |-> lfsr_data == seed[7:0]);

  // Functional correctness: single golden next-state property with proper priority
  default disable iff (!reset_n);

  let step8 (logic [7:0] v) = {v[6], v[5], v[4], (v[3]^v[7]), (v[2]^v[7]), (v[1]^v[7]), v[0], v[7]};

  a_next_state_mux:
    assert property (
      1 |=> lfsr_data ==
            ( !$past(enable)        ? seed[7:0] :
              $past(load)           ? $past(ldata) :
              $past(pause)          ? $past(lfsr_data) :
                                      step8($past(lfsr_data)) )
    );

  // Minimal functional coverage
  c_step:                cover property (enable && !load && !pause);
  c_pause_hold:          cover property (enable && !load &&  pause);
  c_load:                cover property (enable &&  load);
  c_disable_overrides:   cover property (!enable && load);
  c_three_steps:         cover property ((enable && !load && !pause)[*3]);

endmodule

bind ram_controller_ex_lfsr8
  ram_controller_ex_lfsr8_sva #(.seed(seed))
  i_ram_controller_ex_lfsr8_sva (.*,.lfsr_data(lfsr_data));