// Bind SVA to the DUT
bind rising_edge_detector rising_edge_detector_sva sva_inst();

module rising_edge_detector_sva;
  // Access DUT signals directly via bind scope
  // clk, in, anyedge, reg1, reg2, reg3 are in scope here

  default clocking @(posedge clk); endclocking

  // History-valid flags to avoid $past hazards at time 0/1
  bit h1, h2;
  always_ff @(posedge clk) begin
    h1 <= 1'b1;
    h2 <= h1;
  end

  // Pipeline integrity
  ap_reg1: assert property (disable iff (!h1) reg1 == $past(in));
  ap_reg2: assert property (disable iff (!h2) reg2 == $past(reg1));
  ap_reg3: assert property (disable iff (!h1) reg3 == $past(reg2));

  // Core functionality (both structural and input-history views)
  ap_eq_struct: assert property (disable iff (!h1) anyedge == ((reg1 ^ reg2) & reg3));
  ap_eq_input : assert property (disable iff (!h2) anyedge == ((in ^ $past(in)) & $past(in,2)));

  // X-propagation guard: known inputs over 2 cycles imply known output
  ap_no_x: assert property (disable iff (!h2)
                            !$isunknown({in, $past(in), $past(in,2)}) |-> !$isunknown(anyedge));

  // Concise coverage: ensure both edge types are observable on each bit
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : gen_cov
      cover_rise_i:  cover property (h1 && reg3[i] && ~reg2[i] &&  reg1[i] && anyedge[i]);
      cover_fall_i:  cover property (h1 && reg3[i] &&  reg2[i] && ~reg1[i] && anyedge[i]);
      cover_mask_i:  cover property (h1 && ~reg3[i] && !anyedge[i]);
    end
  endgenerate
endmodule