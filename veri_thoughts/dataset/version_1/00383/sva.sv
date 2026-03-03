// SVA for dff_sscan
module dff_sscan_sva #(parameter SIZE=1)
(
  input  logic                  clk,
  input  logic                  se,
  input  logic [SIZE-1:0]       din,
  input  logic [SIZE-1:0]       si,
  input  logic [SIZE-1:0]       q,
  input  logic [SIZE-1:0]       so
);
  default clocking @(posedge clk); endclocking

`ifdef CONNECT_SHADOW_SCAN
  // Next-state check (scan mux)
  ap_q_next_mux: assert property (disable iff ($initstate)
                                  q == $past(se ? si : din))
    else $error("q != $past(se?si:din)");

  // so mirrors q
  ap_so_eq_q: assert property (disable iff ($initstate) so == q)
    else $error("so != q");

  // Functional and scan path coverage
  cp_func_path: cover property (disable iff ($initstate) !se ##1 q == $past(din));
  cp_scan_path: cover property (disable iff ($initstate)  se ##1 q == $past(si));

  // Exercise se toggling
  cp_se_toggle: cover property (disable iff ($initstate) se ##1 !se ##1 se);

  // Bit-level toggle coverage
  genvar i;
  generate
    for (i=0; i<SIZE; i++) begin : COV_Q_BITS
      cp_q_rise: cover property (disable iff ($initstate) $rose(q[i]));
      cp_q_fall: cover property (disable iff ($initstate) $fell(q[i]));
    end
  endgenerate
`else
  // Next-state check (no scan mux)
  ap_q_next_func: assert property (disable iff ($initstate)
                                   q == $past(din))
    else $error("q != $past(din)");

  // so is tied to zero
  ap_so_zero: assert property (so == {SIZE{1'b0}})
    else $error("so != 0 when scan disabled");

  // Coverage: functional updates and q toggles
  cp_func_update: cover property (disable iff ($initstate) q == $past(din));

  genvar j;
  generate
    for (j=0; j<SIZE; j++) begin : COV_Q_BITS_NOSCAN
      cp_q_rise: cover property (disable iff ($initstate) $rose(q[j]));
      cp_q_fall: cover property (disable iff ($initstate) $fell(q[j]));
    end
  endgenerate
`endif
endmodule

// Bind into DUT
bind dff_sscan dff_sscan_sva #(.SIZE(SIZE)) dff_sscan_sva_i
(
  .clk(clk),
  .se(se),
  .din(din),
  .si(si),
  .q(q),
  .so(so)
);