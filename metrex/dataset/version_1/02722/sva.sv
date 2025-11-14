// SVA for trafficLightController
// Bind example (in TB or a package):
// bind trafficLightController trafficLightController_sva sva (.*);

module trafficLightController_sva
(
  input logic        clk,
  input logic        clr,
  input logic [5:0]  lights,
  input logic [2:0]  state,
  input logic [3:0]  count
);
  // Mirror DUT params
  localparam logic [2:0] S0=3'b000, S1=3'b001, S2=3'b010, S3=3'b011, S4=3'b100, S5=3'b101;
  localparam int SEC5 = 5;
  localparam int SEC1 = 1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (clr);

  // Basic sanity and async reset
  ap_async_rst_sc: assert property (@(posedge clr) state==S0 && count==0);
  ap_async_rst_l : assert property (@(posedge clr) lights==6'b100001);
  ap_state_valid : assert property (state inside {S0,S1,S2,S3,S4,S5});
  ap_no_unknowns : assert property (!$isunknown({state,count,lights}));

  // Output decode: state -> lights
  a_dec_s0: assert property ((state==S0) |-> lights==6'b100001);
  a_dec_s1: assert property ((state==S1) |-> lights==6'b100010);
  a_dec_s2: assert property ((state==S2) |-> lights==6'b100100);
  a_dec_s3: assert property ((state==S3) |-> lights==6'b001100);
  a_dec_s4: assert property ((state==S4) |-> lights==6'b010100);
  a_dec_s5: assert property ((state==S5) |-> lights==6'b100100);

  // Output decode: lights -> allowed state(s)
  a_inv_l0: assert property ((lights==6'b100001) |-> state==S0);
  a_inv_l1: assert property ((lights==6'b100010) |-> state==S1);
  a_inv_l2: assert property ((lights==6'b001100) |-> state==S3);
  a_inv_l3: assert property ((lights==6'b010100) |-> state==S4);
  a_inv_l4: assert property ((lights==6'b100100) |-> state inside {S2,S5});

  // Count bounds per state
  a_cnt_bnd_s0: assert property ((state==S0) |-> count<=SEC5);
  a_cnt_bnd_s3: assert property ((state==S3) |-> count<=SEC5);
  a_cnt_bnd_s1: assert property ((state==S1) |-> count<=SEC1);
  a_cnt_bnd_s2: assert property ((state==S2) |-> count<=SEC1);
  a_cnt_bnd_s4: assert property ((state==S4) |-> count<=SEC1);
  a_cnt_bnd_s5: assert property ((state==S5) |-> count<=SEC1);

  // If below threshold, stay in same state next cycle
  a_stay_s0: assert property ((state==S0 && count<SEC5) |=> state==S0);
  a_stay_s3: assert property ((state==S3 && count<SEC5) |=> state==S3);
  a_stay_s1: assert property ((state==S1 && count<SEC1) |=> state==S1);
  a_stay_s2: assert property ((state==S2 && count<SEC1) |=> state==S2);
  a_stay_s4: assert property ((state==S4 && count<SEC1) |=> state==S4);
  a_stay_s5: assert property ((state==S5 && count<SEC1) |=> state==S5);

  // On any state change, counter must be cleared
  a_entry_cnt0: assert property ((state != $past(state)) |-> (count==0));

  // Exact dwell and next-state sequencing
  a_seq_s0: assert property (
      (state==S0 && count==0)
  ##1 (state==S0 && count==1)
  ##1 (state==S0 && count==2)
  ##1 (state==S0 && count==3)
  ##1 (state==S0 && count==4)
  ##1 (state==S0 && count==5)
  ##1 (state==S1 && count==0)
  );

  a_seq_s1: assert property (
      (state==S1 && count==0)
  ##1 (state==S1 && count==1)
  ##1 (state==S2 && count==0)
  );

  a_seq_s2: assert property (
      (state==S2 && count==0)
  ##1 (state==S2 && count==1)
  ##1 (state==S3 && count==0)
  );

  a_seq_s3: assert property (
      (state==S3 && count==0)
  ##1 (state==S3 && count==1)
  ##1 (state==S3 && count==2)
  ##1 (state==S3 && count==3)
  ##1 (state==S3 && count==4)
  ##1 (state==S3 && count==5)
  ##1 (state==S4 && count==0)
  );

  a_seq_s4: assert property (
      (state==S4 && count==0)
  ##1 (state==S4 && count==1)
  ##1 (state==S5 && count==0)
  );

  a_seq_s5: assert property (
      (state==S5 && count==0)
  ##1 (state==S5 && count==1)
  ##1 (state==S0 && count==0)
  );

  // Coverage: visit all states in correct order with required dwell
  c_full_cycle: cover property (
      (state==S0 && count==0)
  ##1 (state==S0 && count==1)
  ##1 (state==S0 && count==2)
  ##1 (state==S0 && count==3)
  ##1 (state==S0 && count==4)
  ##1 (state==S0 && count==5)
  ##1 (state==S1 && count==0)
  ##1 (state==S1 && count==1)
  ##1 (state==S2 && count==0)
  ##1 (state==S2 && count==1)
  ##1 (state==S3 && count==0)
  ##1 (state==S3 && count==1)
  ##1 (state==S3 && count==2)
  ##1 (state==S3 && count==3)
  ##1 (state==S3 && count==4)
  ##1 (state==S3 && count==5)
  ##1 (state==S4 && count==0)
  ##1 (state==S4 && count==1)
  ##1 (state==S5 && count==0)
  ##1 (state==S5 && count==1)
  ##1 (state==S0 && count==0)
  );

  // Coverage: see every lights pattern
  c_lights_s0: cover property (lights==6'b100001);
  c_lights_s1: cover property (lights==6'b100010);
  c_lights_s2s5: cover property (lights==6'b100100);
  c_lights_s3: cover property (lights==6'b001100);
  c_lights_s4: cover property (lights==6'b010100);

endmodule