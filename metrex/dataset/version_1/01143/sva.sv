// SVA checker for matrix_multiplier
module matrix_multiplier_sva (
  input logic [3:0] in1,
  input logic [3:0] in2,
  input logic       enable,
  input logic [3:0] out
);
  // Full product to check truncation behavior
  logic [7:0] prod;
  assign prod = in1 * in2;

  // Functional equivalence (allow delta-cycle settle with ##0)
  property p_out_functional;
    @(in1 or in2 or enable or out)
      disable iff ($isunknown({in1,in2,enable}))
      1'b1 |-> ##0 (out == (enable ? prod[3:0] : 4'h0));
  endproperty
  assert property (p_out_functional)
    else $error("out != (enable ? (in1*in2)[3:0] : 0)");

  // Out must be known whenever inputs are known
  property p_out_known_when_inputs_known;
    @(in1 or in2 or enable or out)
      (!$isunknown({in1,in2,enable})) |-> ##0 (!$isunknown(out));
  endproperty
  assert property (p_out_known_when_inputs_known)
    else $error("out has X/Z with known inputs");

  // Basic functional coverage
  // Enable toggles
  cover property (@(posedge enable) 1);
  cover property (@(negedge enable) 1);

  // Disabled path exercised
  cover property (@(in1 or in2 or enable) !enable && out == 4'h0);

  // Zero product when enabled
  cover property (@(in1 or in2 or enable) enable && (prod == 8'h00) && out == 4'h00);

  // Truncation/overflow scenario when enabled (upper 4 bits non-zero)
  cover property (@(in1 or in2 or enable) enable && (prod[7:4] != 4'h0) && (out == prod[3:0]));

  // Max corner
  cover property (@(in1 or in2 or enable) enable && (in1==4'hF) && (in2==4'hF));
endmodule

// Bind into the DUT
bind matrix_multiplier matrix_multiplier_sva sva_mm (.*);