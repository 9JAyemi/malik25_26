// SVA for manchester
module manchester_sva (manchester dut);

  default clocking @(posedge dut.in); endclocking

  // Functional behavior (mirrors RTL branch on in == prev_in)
  property p_func_toggle;
    (dut.in == $past(dut.prev_in,1,1'b0)) |-> dut.out == ~$past(dut.out,1,1'b0);
  endproperty
  property p_func_set;
    (dut.in != $past(dut.prev_in,1,1'b0)) |-> dut.out == dut.in;
  endproperty
  assert property (p_func_toggle);
  assert property (p_func_set);

  // State/consistency checks
  assert property (dut.prev_in == dut.in);         // prev_in updates to current in at posedge
  assert property (dut.out == dut.out_reg);        // continuous assign integrity

  // No spurious out changes (out only changes on posedge of in)
  assert property (@(posedge dut.out or negedge dut.out) $rose(dut.in));

  // Coverage
  cover property (p_func_set);                     // else-branch taken
  cover property (p_func_toggle);                  // toggle-branch taken
  sequence toggled; (dut.out != $past(dut.out,1,1'b0)); endsequence
  cover property (toggled ##1 toggled);            // two consecutive toggles

endmodule

bind manchester manchester_sva u_manchester_sva (.dut());