// SVA for nand2 and nand4
// Focused, power-aware (for nand4), comprehensive yet concise

// Generic checker for any nand2 instance
module nand2_sva ();
  // Trigger on any relevant change
  property p_func;
    @(A or B or Y) !$isunknown({A,B}) |-> (Y == ~(A & B));
  endproperty
  assert property (p_func);

  // Basic coverage of all AB combinations and both Y values
  for (genvar i = 0; i < 4; i++) begin : cov_ab
    cover property (@(A or B) !$isunknown({A,B}) && {A,B} == i[1:0]);
  end
  cover property (@(Y) !$isunknown(Y) && Y==1'b0);
  cover property (@(Y) !$isunknown(Y) && Y==1'b1);
endmodule

bind nand2 nand2_sva n2_chk();

// Top-level checker for nand4
module nand4_sva ();
  // Define power-good; gate checks under legal power
  wire power_good = (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);

  // Overall functional equivalence: Y == (~(A&B)) & (~(C&D))
  property p_func_overall;
    @(A or B or C or D or Y)
      disable iff (!power_good)
      (!$isunknown({A,B,C,D})) |-> (Y == ((~(A & B)) & (~(C & D))));
  endproperty
  assert property (p_func_overall);

  // Check last stage really inverts nand3_out (since identical inputs to nand4 gate)
  property p_last_is_inverter;
    @(nand3_out or Y)
      disable iff (!power_good)
      (!$isunknown(nand3_out)) |-> (Y == ~nand3_out);
  endproperty
  assert property (p_last_is_inverter);

  // Optional internal stage sanity (kept concise; nand2_sva already checks each nand2)
  property p_mid_func;
    @(nand1_out or nand2_out or nand3_out)
      disable iff (!power_good)
      (!$isunknown({nand1_out,nand2_out})) |-> (nand3_out == ~(nand1_out & nand2_out));
  endproperty
  assert property (p_mid_func);

  // Known-ness propagation to Y under known inputs
  property p_known_y;
    @(A or B or C or D or Y)
      disable iff (!power_good)
      (!$isunknown({A,B,C,D})) |-> !$isunknown(Y);
  endproperty
  assert property (p_known_y);

  // Coverage: all 16 input combinations; both Y=0 and Y=1; Y toggles
  for (genvar i = 0; i < 16; i++) begin : cov_all_inputs
    cover property (@(A or B or C or D)
                    power_good && !$isunknown({A,B,C,D}) && {A,B,C,D} == i[3:0]);
  end
  cover property (@(Y) power_good && !$isunknown(Y) && Y==1'b0);
  cover property (@(Y) power_good && !$isunknown(Y) && Y==1'b1);
  cover property (@(Y) power_good ##1 Y);              // any toggle
  cover property (@(Y) power_good and (Y==0) ##1 (Y==1));
  cover property (@(Y) power_good and (Y==1) ##1 (Y==0));

  // Power-good seen
  cover property (@(VPWR or VGND or VPB or VNB) power_good);
endmodule

bind nand4 nand4_sva n4_chk();