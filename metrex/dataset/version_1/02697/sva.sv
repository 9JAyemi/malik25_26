// SVA for v89d234_v9148cb (the register block)
module v89d234_v9148cb_sva (
  input logic        clk,
  input logic        load,
  input logic [7:0]  d,
  input logic [7:0]  q
);
  default clocking cb @(posedge clk); default input #1step output #0; endclocking

  // Correct capture on load
  ap_cap:  assert property (load |-> (q == d));

  // Hold value when not loading
  ap_hold: assert property (!load |-> (q == $past(q,1,q)));

  // Output may change only when load is asserted at that edge
  ap_change_requires_load: assert property ($changed(q) |-> load);

  // Coverage
  cp_load:           cover property (load);
  cp_hold:           cover property (!load);
  cp_two_loads_diff: cover property (load ##1 load and (d != $past(d,1,'0)));
endmodule

bind v89d234_v9148cb v89d234_v9148cb_sva u_v89d234_v9148cb_sva (.clk(clk), .load(load), .d(d), .q(q));


// SVA for top-level wrapper v89d234 (checks connectivity and endianness)
module v89d234_sva (
  input logic        v41eb95,     // clk
  input logic [7:0]  v39f831,     // d
  input logic        vf892a0,     // load
  input logic [7:0]  vb1c024      // q (output)
);
  default clocking cb @(posedge v41eb95); default input #1step output #0; endclocking

  // Wrapper preserves data order: on load, output equals input data
  ap_wrap_cap:  assert property (vf892a0 |-> (vb1c024 == v39f831));

  // Wrapper holds output when not loading
  ap_wrap_hold: assert property (!vf892a0 |-> (vb1c024 == $past(vb1c024,1,vb1c024)));

  // Output changes only on a load edge
  ap_wrap_change_requires_load: assert property ($changed(vb1c024) |-> vf892a0);

  // Coverage
  cp_wrap_load:          cover property (vf892a0);
  cp_wrap_hold:          cover property (!vf892a0);
  cp_wrap_load_then_hold: cover property (vf892a0 ##1 !vf892a0);
endmodule

bind v89d234 v89d234_sva u_v89d234_sva (.v41eb95(v41eb95), .v39f831(v39f831), .vf892a0(vf892a0), .vb1c024(vb1c024));