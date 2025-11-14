// Add inside SDP_RAM or bind to it. Focused, concise SVA with key checks and coverage.
`ifndef SDP_RAM_SVA
`define SDP_RAM_SVA
// synopsys translate_off
// pragma translate_off
`ifdef SVA
default clocking cb @(posedge clk); endclocking

// Address range checks (memory depth is 16 -> only [3:0] used)
assert property (cb wce |-> (wa[9:4] == '0)) else $error("WA out of range (>15) when writing");
assert property (cb rce |-> (ra[9:4] == '0)) else $error("RA out of range (>15) when reading");

// Synchronous write must update memory immediately after the edge
assert property (cb wce |-> ##0 memory[wa[3:0]] == wd)
  else $error("Write did not update memory same cycle");

// Read behavior
// rce low forces zero
assert property (cb !rce |-> ##0 (rq == 16'h0))
  else $error("rq not forced to 0 when rce==0");

// rce high returns memory content; handle RAW same-address
assert property (cb rce && wce && (ra[3:0] == wa[3:0]) |-> ##0 (rq == wd))
  else $error("Same-cycle RAW (ra==wa) must return wd");

assert property (cb rce && (!wce || (ra[3:0] != wa[3:0])) |-> ##0 (rq == memory[ra[3:0]]))
  else $error("Read data mismatch");

// No unintended writes to other locations on a write
genvar i;
generate
  for (i = 0; i < 16; i++) begin : G_NO_SPURIOUS_WRITES
    assert property (cb wce && (wa[3:0] != i[3:0]) |-> ##0 $stable(memory[i]))
      else $error("Spurious write observed at memory[%0d]", i);
  end
endgenerate

// Functional coverage
cover property (cb wce);
cover property (cb rce);
cover property (cb rce && wce && (ra[3:0] == wa[3:0]));   // same-cycle RAW
cover property (cb rce && wce && (ra[3:0] != wa[3:0]));   // read while writing different addr
generate
  genvar j;
  for (j = 0; j < 16; j++) begin : G_ADDR_COV
    cover property (cb wce && (wa[3:0] == j));
    cover property (cb rce && (ra[3:0] == j));
  end
endgenerate
`endif
// pragma translate_on
// synopsys translate_on
`endif