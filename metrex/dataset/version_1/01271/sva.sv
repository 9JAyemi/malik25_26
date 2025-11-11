// SVA for scale_1d
// Bind inside the DUT to access internal signals (s_cnt, m_cnt, s_idx, m_idx, running, last, progress, next, s_addr)
module scale_1d_sva #(
  parameter int C_M_WIDTH = 12,
  parameter int C_S_WIDTH = 10,
  parameter int C_S_ADDR_WIDTH = 32
) ();
  default clocking cb @(posedge clk); endclocking
  default disable iff (!resetn);

  // Environment assumptions (avoid degenerate cases)
  assume property (start |-> (m_width > 0) && (s_width > 0));

  // Combinational definitions
  assert property (progress == (!o_valid || o_ready));
  assert property (next     == ( o_valid && o_ready));
  assert property (o_valid  == (running && (s_cnt >= m_cnt)));

  // Reset values held while in reset
  assert property (!resetn |-> (running==0 && last==0 && s_cnt==0 && m_cnt==0 && s_idx==0 && m_idx==0 && s_addr==0));

  // Start initialization (start has highest priority)
  assert property (start |=> (running && !last &&
                              s_cnt==m_width && m_cnt==s_width &&
                              s_idx==0 && m_idx==0 &&
                              s_addr==s_base_addr + s_off_addr));

  // State holds during stall (unless start overrides)
  assert property (o_valid && !o_ready && !start |=> $stable({s_cnt,m_cnt,s_idx,m_idx,s_addr,last,running}));

  // Monotonicity and exact updates under progress (unless start overrides)
  // m path always advances on next
  assert property (next && !start |=> m_idx == $past(m_idx) + 1);
  assert property (running && (!o_valid || o_ready) && !start && (s_cnt >= m_cnt)
                   |=> (m_cnt == $past(m_cnt) + s_width) && (m_idx == $past(m_idx) + 1));

  // s path advances when s_cnt <= m_cnt
  assert property (running && (!o_valid || o_ready) && !start && (s_cnt <= m_cnt)
                   |=> (s_cnt == $past(s_cnt) + m_width) &&
                       (s_idx == $past(s_idx) + 1) &&
                       (s_addr == $past(s_addr) + s_inc_addr));

  // Address <-> s_idx coupling
  assert property ((s_addr != $past(s_addr)) |-> (s_addr == $past(s_addr) + s_inc_addr && s_idx == $past(s_idx) + 1));
  assert property ((s_idx  != $past(s_idx )) |-> (s_addr == $past(s_addr) + s_inc_addr));

  // Index bounds (inclusive upper bound due to final increment)
  assert property (m_idx <= m_width);
  assert property (s_idx <= s_width);

  // Running lifecycle
  assert property (!$past(running) && running |-> $past(start)); // only rises on start
  assert property ($past(running) && !running |-> $past(next && (m_idx == m_width-1)) || $past(!resetn)); // only falls on final next (or reset)
  assert property (running && !start && !(next && (m_idx == m_width-1)) |=> running); // sticky while active

  // Last lifecycle
  assert property (start |=> !last);
  // Only set by penultimate transfer (guard small m_width)
  assert property ((!$past(last) && last) |-> ($past(!start) && $past(next) && ($past(m_idx) == m_width-2)));
  // Once set, stays set until next start
  assert property (last && !start |=> last);
  // When last is asserted and a transfer occurs, it must be the final beat
  assert property (last && o_valid && o_ready |-> (m_idx == m_width-1));

  // End-of-transfer effects (guard against simultaneous start)
  assert property (next && (m_idx == m_width-1) && !start |=> !running);
  assert property (next && (m_idx == m_width-2) && !start |=> last);

  // Functional coverage
  cover property (start ##1 running ##[1:$] (o_valid && !o_ready) ##1 (o_valid && o_ready));
  cover property (start ##[1:$] (running && (s_cnt == m_cnt)) ##1 next);           // equality case
  cover property (start ##[1:$] (running && (s_cnt <  m_cnt)) ##1 (!o_valid));      // s step
  cover property (start ##[1:$] (running && (s_cnt >  m_cnt)) ##1  o_valid);        // m step
  cover property (start ##[1:$] (last && o_valid && o_ready) ##1 !running);         // observe last transfer end
endmodule

bind scale_1d scale_1d_sva #(.C_M_WIDTH(C_M_WIDTH),
                             .C_S_WIDTH(C_S_WIDTH),
                             .C_S_ADDR_WIDTH(C_S_ADDR_WIDTH)) u_scale_1d_sva();