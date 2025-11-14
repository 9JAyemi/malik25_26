// SVA for data_generator — concise, high-quality checks and coverage
module data_generator_sva
  #(int R1W=255, R2W=256, R3W=257)
  (input logic                 CLK,
   input logic                 CE,
   input logic                 D1,
   input logic                 D2,
   input logic [R1W-1:0]       ring1,
   input logic [R2W-1:0]       ring2,
   input logic [R3W-1:0]       ring3);

  default clocking cb @(posedge CLK); endclocking

  // Guard for $past
  logic started;
  initial started = 1'b0;
  always_ff @(posedge CLK) started <= 1'b1;

  // Basic sanity: no X/Z after first sampled cycle
  a_known: assert property (started |-> !$isunknown({CE, ring1, ring2, ring3, D1, D2}));

  // Outputs equal specified XORs
  a_d1_def: assert property (D1 == (ring1[0] ^ ring2[0]));
  a_d2_def: assert property (D2 == (ring2[0] ^ ring3[0]));

  // CE gating: hold when CE==0
  a_hold_r1: assert property (disable iff (!started) !CE |-> ring1 == $past(ring1));
  a_hold_r2: assert property (disable iff (!started) !CE |-> ring2 == $past(ring2));
  a_hold_r3: assert property (disable iff (!started) !CE |-> ring3 == $past(ring3));

  // Rotation when CE==1
  a_rot_r1: assert property (disable iff (!started)
                             CE |-> ring1 == { $past(ring1[0]), $past(ring1[R1W-1:1]) });
  a_rot_r2: assert property (disable iff (!started)
                             CE |-> ring2 == { $past(ring2[0]), $past(ring2[R2W-1:1]) });
  a_rot_r3: assert property (disable iff (!started)
                             CE |-> ring3 == { $past(ring3[0]), $past(ring3[R3W-1:1]) });

  // Rotation preserves population count
  a_pop_r1: assert property (disable iff (!started) $countones(ring1) == $past($countones(ring1)));
  a_pop_r2: assert property (disable iff (!started) $countones(ring2) == $past($countones(ring2)));
  a_pop_r3: assert property (disable iff (!started) $countones(ring3) == $past($countones(ring3)));

  // Output next-state consistency when CE==1 (end-to-end check)
  a_d1_next: assert property (disable iff (!started)
                              CE |-> D1 == $past(ring1[1] ^ ring2[1]));
  a_d2_next: assert property (disable iff (!started)
                              CE |-> D2 == $past(ring2[1] ^ ring3[1]));

  // Coverage
  c_ce_toggle: cover property (!CE ##1 CE ##1 !CE);
  c_d1_0:      cover property (D1 == 1'b0);
  c_d1_1:      cover property (D1 == 1'b1);
  c_d2_0:      cover property (D2 == 1'b0);
  c_d2_1:      cover property (D2 == 1'b1);

  // Cover full-cycle wrap (pattern returns after width CE-high cycles)
  c_wrap_r1: cover property (started and CE[*R1W] and ring1 == $past(ring1, R1W));
  c_wrap_r2: cover property (started and CE[*R2W] and ring2 == $past(ring2, R2W));
  c_wrap_r3: cover property (started and CE[*R3W] and ring3 == $past(ring3, R3W));

endmodule

// Bind into the DUT (connects to internals by name)
bind data_generator data_generator_sva #(.R1W(255), .R2W(256), .R3W(257)) data_generator_sva_i (.*);