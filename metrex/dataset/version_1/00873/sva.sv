// SVA for the provided design. Bind this file in your sim.
// Concise, high-quality checks with essential coverage.

module top_module_sva;
  // This module is bound into top_module scope; ports are visible hierarchically.
  default clocking cb @(posedge clk); endclocking

  // Guard for $past(...,2)
  logic [1:0] init_cnt;
  logic past2_valid;
  initial begin init_cnt = 0; past2_valid = 0; end
  always_ff @(posedge clk) begin
    if (!past2_valid) begin
      init_cnt    <= init_cnt + 1;
      past2_valid <= (init_cnt == 2-1);
    end
  end

  // Binary adder correctness (carry+sum exact)
  a_adder_correct:
    assert property ( {cout, sum} === ({1'b0, b} + {cin, a}) );

  // Functional module mapping (note zero-extension to 103 bits)
  a_out_concat_correct:
    assert property ( out === {2'b00, sum, q} );

  // Shift register behavior: q is d delayed by 2 cycles
  a_shift_delay_2:
    assert property ( past2_valid |-> ( q === $past(d,2) ) );

  // No glitches on q between rising edges
  a_q_no_glitch:
    assert property (@(negedge clk) $stable(q));

  // Redundant but explicit: top two bits of out are always 0 due to width extension
  a_out_top_zero:
    assert property ( out[102:101] === 2'b00 );

  // ----------------
  // Coverage
  // ----------------
  // Trivial add (all zeros)
  c_adder_zero:
    cover property ( !cin && (a == 100'b0) && (b == 100'b0) && (cout == 1'b0) && (sum == 100'b0) );

  // Observe carry-out with and without cin
  c_carry_out_wo_cin:
    cover property ( !cin && cout );
  c_carry_out_with_cin:
    cover property ( cin && cout );

  // Boundary-like case: max a, zero b, no carry expected when cin=0
  c_sum_all_ones_no_carry_when_b_zero:
    cover property ( (a == {100{1'b1}}) && (b == 100'b0) && !cin && !cout );

  // See the 2-cycle delay relationship exercised
  c_q_delays_d:
    cover property ( past2_valid && (q === $past(d,2)) );

  // q edges
  c_q_edges_rise:
    cover property (@(posedge clk) $rose(q));
  c_q_edges_fall:
    cover property (@(posedge clk) $fell(q));

  // Out mapping seen (sanity)
  c_out_mapping_seen:
    cover property ( out === {2'b00, sum, q} );

endmodule

bind top_module top_module_sva top_module_sva_i();