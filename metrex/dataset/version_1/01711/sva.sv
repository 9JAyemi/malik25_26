// SVA checker for integer_to_segment
module integer_to_segment_sva (
  input logic [3:0] int_data,
  input logic [7:0] seg_data
);

  // Reference encoder (mirrors DUT truth table)
  function automatic logic [7:0] enc (input logic [3:0] v);
    case (v)
      4'h0: enc = 8'hC0; 4'h1: enc = 8'hF9; 4'h2: enc = 8'hA4; 4'h3: enc = 8'hB0;
      4'h4: enc = 8'h99; 4'h5: enc = 8'h92; 4'h6: enc = 8'h82; 4'h7: enc = 8'hF8;
      4'h8: enc = 8'h80; 4'h9: enc = 8'h90; 4'hA: enc = 8'h88; 4'hB: enc = 8'h83;
      4'hC: enc = 8'hC6; 4'hD: enc = 8'hA1; 4'hE: enc = 8'h86; 4'hF: enc = 8'h8E;
      default: enc = 8'hFF;
    endcase
  endfunction

  // Combinational sampling event (fires on any I/O change)
  event comb_ev; always @(int_data or seg_data) -> comb_ev;

  // Functional correctness for known inputs
  property p_map_known;
    @(comb_ev) !($isunknown(int_data)) |-> (seg_data == enc(int_data));
  endproperty
  assert property (p_map_known);

  // Default/unknown handling: X/Z on int_data drives 0xFF
  property p_map_unknown;
    @(comb_ev) $isunknown(int_data) |-> (seg_data == 8'hFF);
  endproperty
  assert property (p_map_unknown);

  // Output must never be X/Z
  property p_seg_known;
    @(comb_ev) !($isunknown(seg_data));
  endproperty
  assert property (p_seg_known);

  // No spurious output toggles without input change
  property p_no_glitch;
    @(comb_ev) $changed(seg_data) |-> $changed(int_data);
  endproperty
  assert property (p_no_glitch);

  // Coverage: see each 0-F encoding at least once; also see default on unknown
  genvar v;
  generate
    for (v = 0; v < 16; v++) begin : cov_lut
      cover property (@(comb_ev) (int_data == v[3:0]) && (seg_data == enc(v[3:0])));
    end
  endgenerate
  cover property (@(comb_ev) $isunknown(int_data) && seg_data == 8'hFF);

endmodule

// Bind into DUT
bind integer_to_segment integer_to_segment_sva u_integer_to_segment_sva (
  .int_data(int_data),
  .seg_data(seg_data)
);