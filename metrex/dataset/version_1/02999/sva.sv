// SVA for oh_clockmux: concise, high-quality checks and coverage
// Bind this file alongside the DUT

module oh_clockmux_sva #(
  parameter int N = 1,
  parameter bit REQ_ONEHOT = 1  // set 0 to disable onehot0 check
)(
  input  logic [N-1:0] en,
  input  logic [N-1:0] clkin,
  input  logic         clkout
);

  // Golden reference (combinational spec)
  logic ref_clkout;
  assign ref_clkout = |(clkin & en);

  // ASIC configuration sanity
`ifdef CFG_ASIC
  initial begin
    if (!(N==2 || N==4))
      $error("oh_clockmux(N=%0d): CFG_ASIC requires N==2 or N==4", N);
  end
`endif

  genvar i;

  // Functional equivalence at all relevant edges; use ##0 to sample after settle
  generate
    for (i=0; i<N; i++) begin : g_func_eq_in
      property p_ref_on_in_edge;
        @(posedge clkin[i] or negedge clkin[i] or posedge en[i] or negedge en[i])
          1 |-> ##0 (clkout == ref_clkout);
      endproperty
      assert property (p_ref_on_in_edge);
    end
  endgenerate

  property p_ref_on_out_edge;
    @(posedge clkout or negedge clkout) 1 |-> ##0 (clkout == ref_clkout);
  endproperty
  assert property (p_ref_on_out_edge);

  // All enables low forces output low
  generate
    for (i=0; i<N; i++) begin : g_zero_en_low
      assert property (@(posedge en[i] or negedge en[i])
                        (en == '0) |-> ##0 (clkout == 1'b0));
    end
  endgenerate

  // Optional at-most-one enable high (recommended for clock-mux correctness)
  generate
    if (REQ_ONEHOT) begin : g_onehot
      for (i=0; i<N; i++) begin : g_oh
        assert property (@(posedge en[i] or negedge en[i]) $onehot0(en))
          else $error("oh_clockmux: en not onehot0: %b", en);
      end
    end
  endgenerate

  // No X/Z on output when inputs are known
  generate
    for (i=0; i<N; i++) begin : g_no_x
      assert property (@(posedge clkin[i] or negedge clkin[i] or posedge en[i] or negedge en[i])
                        (! $isunknown({en,clkin})) |-> ##0 (! $isunknown(clkout)));
    end
  endgenerate

  // Coverage: each input selected drives an output edge
  generate
    for (i=0; i<N; i++) begin : g_cov_sel_i
      cover property (@(posedge clkin[i] or negedge clkin[i])
                       (en == (1'b1 << i)) ##0 $changed(clkout));
    end
  endgenerate

endmodule

// Bind to all instances of oh_clockmux; N is taken from the bound instance
bind oh_clockmux oh_clockmux_sva #(.N(N)) oh_clockmux_sva_b (.en(en), .clkin(clkin), .clkout(clkout));