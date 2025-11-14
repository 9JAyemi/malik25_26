// SVA for next_higher_binary: concise, full functional check + coverage

module next_higher_binary_sva(
  input logic [3:0] in,
  input logic [3:0] out
);

  // Sample on any change of inputs/outputs (combinational DUT)
  default clocking cb @(in or out); endclocking

  function automatic logic [3:0] inc4(input logic [3:0] v);
    inc4 = v + 4'h1; // wraps naturally to 4 bits
  endfunction

  // Functional correctness: out is in+1 (mod 16)
  a_inc:       assert property (out == inc4(in));

  // No spurious output changes without an input change
  a_no_spur:   assert property ($changed(out) |-> $changed(in));

  // Knownness: input must be 2-state; output must be 2-state when input is 2-state
  a_in_known:  assert property (!$isunknown(in));
  a_out_known: assert property (!$isunknown(in) |-> !$isunknown(out));

  // Full functional coverage: all 16 mappings, including wrap
  genvar i;
  generate
    for (i=0; i<16; i++) begin : COV
      localparam logic [3:0] VIN  = i[3:0];
      localparam logic [3:0] VOUT = (i+1) & 4'hF;
      c_map: cover property (in == VIN && out == VOUT);
    end
  endgenerate
  c_wrap: cover property (in == 4'hF && out == 4'h0);

endmodule

bind next_higher_binary next_higher_binary_sva sva_i(.in(in), .out(out));