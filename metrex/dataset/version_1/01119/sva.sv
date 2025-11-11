// SVA for spm/TCMP/CSADD
// Bind these assertions to the RTL without modifying the DUT

// Assertions for CSADD: functional next-state, reset/ld behavior, X-checks, minimal coverage
module csadd_sva;
  default clocking cb @(posedge clk); endclocking

  // Reset drives state low in same clock; ld clears in next clock
  a_csadd_rst: assert property (rst |-> (sum==1'b0 && sc==1'b0));
  a_csadd_ld : assert property (disable iff (rst) ld |=> (sum==1'b0 && sc==1'b0));

  // Next-state functional correctness (uses old sc,x,y)
  a_csadd_next: assert property (disable iff (rst)
                                 !ld |=> (sum == ($past(x) ^ $past(y) ^ $past(sc)) &&
                                          sc  == (($past(y) & $past(sc)) ^ ($past(x) & ($past(y) ^ $past(sc))))));

  // Combinational half-adder identities
  a_csadd_comb: assert property (cb 1'b1 |-> (hsum1 == (y ^ sc) &&
                                              hco1  == (y & sc)  &&
                                              hsum2 == (x ^ hsum1) &&
                                              hco2  == (x & hsum1)));

  // No unknowns on output during normal operation
  a_csadd_nox: assert property (disable iff (rst) !$isunknown(sum));

  // Minimal coverage: exercise sum/sc = 1
  c_csadd_sum1:  cover property (disable iff (rst) !ld && (x ^ y ^ sc));
  c_csadd_carry: cover property (disable iff (rst) !ld && ((y & sc) ^ (x & (y ^ sc))));
endmodule

bind CSADD csadd_sva csadd_sva_i();

// Assertions for TCMP: functional next-state, reset/ld behavior, X-checks, minimal coverage
module tcmp_sva;
  default clocking cb @(posedge clk); endclocking

  // Reset drives state low; ld clears next cycle
  a_tcmp_rst: assert property (rst |-> (s==1'b0 && z==1'b0));
  a_tcmp_ld : assert property (disable iff (rst) ld |=> (s==1'b0 && z==1'b0));

  // Next-state functional correctness (uses old z,a)
  a_tcmp_next: assert property (disable iff (rst)
                                !ld |=> (s == ($past(a) ^ $past(z)) &&
                                         z == ($past(a) | $past(z))));

  // No unknowns on output during normal operation
  a_tcmp_nox: assert property (disable iff (rst) !$isunknown(s));

  // Minimal coverage: observe z set and s=1 event
  c_tcmp_zset: cover property (disable iff (rst) !ld && !z ##1 !ld && a ##1 z);
  c_tcmp_s1  : cover property (disable iff (rst) !ld && a ##1 s);
endmodule

bind TCMP tcmp_sva tcmp_sva_i();

// Top-level spm assertions: reset/ld propagation, X-checks, basic activity coverage
module spm_sva;
  default clocking cb @(posedge clk); endclocking

  // All outputs cleared on reset and after ld
  a_spm_rst: assert property (rst |-> (p==1'b0 && pp=='0));
  a_spm_ld : assert property (disable iff (rst) ld |=> (p==1'b0 && pp=='0));

  // No unknowns on outputs during normal operation
  a_spm_nox: assert property (disable iff (rst) (!$isunknown(p) && !$isunknown(pp)));

  // Basic activity coverage: see y toggle and some activity on outputs
  c_spm_y_act: cover property (disable iff (rst) !ld ##1 y ##1 !y);
  c_spm_out1 : cover property (disable iff (rst) !ld && (p || (|pp)));
endmodule

bind spm spm_sva spm_sva_i();