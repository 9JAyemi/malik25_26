// Add this SVA block inside regfile (or bind to it); it uses internal addr/data
`ifndef REGFILE_SVA
`define REGFILE_SVA
// synthesis translate_off
default clocking cb @(posedge clk); endclocking

bit past_valid;
always_ff @(posedge clk) past_valid <= 1'b1;
default disable iff (!past_valid)

// Basic input X checks
assert property (!$isunknown({we, wa, ra}));
assert property (we |-> !$isunknown(wd));

// Out mirrors addr (combinational)
assert property (out == addr);

// Address register behavior
assert property (addr == $past(ra));

// Read data semantics (with same-cycle RAW forwarding)
assert property (rd ==
  ( ($past(we) && ($past(wa) == $past(ra))) ? $past(wd)
                                            : $past(data[$past(ra)]) ));

// Write updates correct location
assert property ($past(we) |-> data[$past(wa)] == $past(wd));

// No spurious/corrupt writes
genvar i;
for (i=0; i<16; i++) begin : mem_integrity
  assert property (!$past(we) |-> data[i] == $past(data[i]));
  assert property ($past(we) && ($past(wa) != i) |-> data[i] == $past(data[i]));
end

// Functional coverage
cover property (we);                         // any write
cover property (we && (wa == ra));           // same-cycle RAW
cover property (!we);                        // idle cycle
for (i=0; i<16; i++) begin : cov_addr
  cover property (we && (wa == i));          // write each address
  cover property (ra == i);                  // read each address
end
cover property (we ##1 we && $past(wa) == wa);  // back-to-back write same addr
cover property (we ##1 we && $past(wa) != wa);  // back-to-back write diff addr
// synthesis translate_on
`endif