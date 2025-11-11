// Drop this block into the module (or bind it) to verify the arbiter.
// Guard with your preferred define if needed.
`ifndef SYNTHESIS
// pragma translate_off
default clocking cb @(posedge i_clk); endclocking
default disable iff (i_rst)

// Basic ownership sanity
assert property (!(w_a_owner && w_b_owner));
assert property (w_a_owner |-> i_a_cyc);
assert property (w_b_owner |-> i_b_cyc);

// o_cyc correctness
assert property ((!r_cyc && !i_a_cyc && !i_b_cyc) |-> !o_cyc);
assert property (o_cyc |-> (w_a_owner ^ w_b_owner));

// Arbitration when idle
assert property ((!r_cyc &&  i_a_cyc && !i_b_cyc) |-> ( w_a_owner && !w_b_owner));
assert property ((!r_cyc && !i_a_cyc &&  i_b_cyc) |-> (!w_a_owner &&  w_b_owner));

// Alternating fairness on simultaneous requests (idle)
assert property ((!r_cyc && i_a_cyc && i_b_cyc) |-> (w_a_owner == !r_a_last_owner) && (w_b_owner == r_a_last_owner));

// r_a_last_owner updates to current winner
assert property ((w_a_owner ^ w_b_owner) |=> (r_a_last_owner == w_a_owner));

// Ownership persistence within a cycle
assert property (r_a_owner && i_a_cyc |-> w_a_owner);
assert property (r_b_owner && i_b_cyc |-> w_b_owner);

// Forward path muxing and strobe rules
assert property (w_a_owner |-> (o_we==i_a_we && o_adr==i_a_adr && o_dat==i_a_dat && o_sel==i_a_sel
                                && o_stb==(o_cyc && i_a_stb)));
assert property (w_b_owner |-> (o_we==i_b_we && o_adr==i_b_adr && o_dat==i_b_dat && o_sel==i_b_sel
                                && o_stb==(o_cyc && i_b_stb)));
assert property (o_stb |-> o_cyc);

// Return path: ack/err/stall routing
assert property (o_a_ack == (w_a_owner && i_ack));
assert property (o_b_ack == (w_b_owner && i_ack));
assert property (o_a_err == (w_a_owner && i_err));
assert property (o_b_err == (w_b_owner && i_err));
assert property ( w_a_owner |-> (o_a_stall == i_stall));
assert property (!w_a_owner |->  o_a_stall);
assert property ( w_b_owner |-> (o_b_stall == i_stall));
assert property (!w_b_owner |->  o_b_stall);

// No stray responses
assert property ((o_a_ack || o_b_ack || o_a_err || o_b_err) |-> o_cyc);
assert property (!(o_a_ack && o_b_ack));
assert property (!(o_a_err && o_b_err));

// Minimal functional coverage
cover property (!r_cyc && i_a_cyc && !i_b_cyc ##1 w_a_owner ##[1:$] i_ack);
cover property (!r_cyc && !i_a_cyc && i_b_cyc ##1 w_b_owner ##[1:$] i_ack);
cover property (r_a_last_owner && !r_cyc && i_a_cyc && i_b_cyc ##1 w_b_owner);
cover property (!r_a_last_owner && !r_cyc && i_a_cyc && i_b_cyc ##1 w_a_owner);
cover property (!r_cyc && i_a_cyc && i_b_cyc ##1 (w_a_owner, w_b_owner)
                ##[1:$] !o_cyc ##1 !r_cyc && i_a_cyc && i_b_cyc ##1 (w_a_owner, w_b_owner)); // alternates on successive arbitrations
// pragma translate_on
`endif