// SVA checker for edge_detector internals and behavior
module edge_detector_sva (
  input logic         clk,
  input logic [7:0]   in,
  input logic [7:0]   anyedge,
  input logic [7:0]   curr,
  input logic [7:0]   prev
);
  // history enables (no reset in DUT)
  logic past1, past2;
  always_ff @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
  end

  default clocking cb @(posedge clk); endclocking

  // Pipeline correctness
  assert_curr_is_past_in:
    assert property (disable iff (!past1) curr == $past(in))
    else $error("curr must equal in delayed by 1 cycle");

  assert_prev_is_past2_in:
    assert property (disable iff (!past2) prev == $past(in,2))
    else $error("prev must equal in delayed by 2 cycles");

  // Edge-detect function (internal and port-level equivalence)
  assert_anyedge_internal_form:
    assert property (disable iff (!past2) anyedge == (curr & ~prev))
    else $error("anyedge must equal curr & ~prev (rising-edge detect on curr)");

  assert_anyedge_vs_in_history:
    assert property (disable iff (!past2) anyedge == ($past(in,1) & ~$past(in,2)))
    else $error("anyedge must reflect rising edges of in with 1-cycle latency");

  // Per-bit properties
  genvar i;
  generate for (i=0; i<8; i++) begin: per_bit
    // Bit-accurate behavior
    assert_bit_func:
      assert property (disable iff (!past2)
                       anyedge[i] == ($past(in[i],1) & ~$past(in[i],2)))
      else $error("anyedge[%0d] mismatch vs in history", i);

    // 1-cycle pulse per edge on that bit
    assert_bit_one_cycle_pulse:
      assert property (disable iff (!past2) anyedge[i] |-> ##1 !anyedge[i])
      else $error("anyedge[%0d] must not persist >1 cycle", i);

    // Covers: rising produces pulse next cycle; falling produces no pulse
    cover_bit_rise_pulses:
      cover property (disable iff (!past2) $rose(in[i]) ##1 anyedge[i]);

    cover_bit_fall_no_pulse:
      cover property (disable iff (!past2) $fell(in[i]) ##1 !anyedge[i]);
  end endgenerate

  // Multi-bit cover: all bits rise together -> full-width pulse next cycle
  cover_all_bits_rise:
    cover property (disable iff (!past2)
                    ($past(in,1) == 8'h00 && in == 8'hFF) ##1 (anyedge == 8'hFF));
endmodule

// Port-only checker (bind to top or anywhere the ports are visible)
module edge_detector_port_sva (
  input logic         clk,
  input logic [7:0]   in,
  input logic [7:0]   anyedge
);
  logic past1, past2;
  always_ff @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
  end

  default clocking cb @(posedge clk); endclocking

  // Behavioral spec at ports
  assert_ports_spec:
    assert property (disable iff (!past2) anyedge == ($past(in,1) & ~$past(in,2)))
    else $error("Port-level spec: anyedge != past(in)&~past2(in)");

  // Per-bit pulse width and cover
  genvar i;
  generate for (i=0; i<8; i++) begin: per_bit_ports
    assert_bit_one_cycle_pulse:
      assert property (disable iff (!past2) anyedge[i] |-> ##1 !anyedge[i]);

    cover_bit_rise_pulses:
      cover property (disable iff (!past2) $rose(in[i]) ##1 anyedge[i]);

    cover_bit_fall_no_pulse:
      cover property (disable iff (!past2) $fell(in[i]) ##1 !anyedge[i]);
  end endgenerate

  cover_all_bits_rise:
    cover property (disable iff (!past2)
                    ($past(in,1) == 8'h00 && in == 8'hFF) ##1 (anyedge == 8'hFF));
endmodule

// Bind checkers
bind edge_detector edge_detector_sva u_edge_detector_sva (
  .clk(clk),
  .in(in),
  .anyedge(anyedge),
  .curr(curr),
  .prev(prev)
);

bind top_module edge_detector_port_sva u_top_edge_detector_port_sva (
  .clk(clk),
  .in(in),
  .anyedge(anyedge)
);