// SVA for my_logic – concise, high-quality checks and coverage
// Bind this checker to the DUT. No DUT/testbench edits required.

`ifndef SYNTHESIS
module my_logic_chk (input logic [3:0] data_in,
                     input logic [3:0] data_out);

  // Reference forward map
  function automatic logic [3:0] ref_map (input logic [3:0] d);
    case (d)
      4'h0: ref_map = 4'h0;
      4'h1: ref_map = 4'hF;
      4'h2: ref_map = 4'h5;
      4'h3: ref_map = 4'hA;
      4'h4: ref_map = 4'h3;
      4'h5: ref_map = 4'hC;
      4'h6: ref_map = 4'h6;
      4'h7: ref_map = 4'h9;
      4'h8: ref_map = 4'hE;
      4'h9: ref_map = 4'h1;
      4'hA: ref_map = 4'hD;
      4'hB: ref_map = 4'h2;
      4'hC: ref_map = 4'h8;
      4'hD: ref_map = 4'h7;
      4'hE: ref_map = 4'hB;
      4'hF: ref_map = 4'h4;
      default: ref_map = 4'hx;
    endcase
  endfunction

  // Inverse map (bijectiveness check)
  function automatic logic [3:0] inv_map (input logic [3:0] q);
    case (q)
      4'h0: inv_map = 4'h0;
      4'hF: inv_map = 4'h1;
      4'h5: inv_map = 4'h2;
      4'hA: inv_map = 4'h3;
      4'h3: inv_map = 4'h4;
      4'hC: inv_map = 4'h5;
      4'h6: inv_map = 4'h6;
      4'h9: inv_map = 4'h7;
      4'hE: inv_map = 4'h8;
      4'h1: inv_map = 4'h9;
      4'hD: inv_map = 4'hA;
      4'h2: inv_map = 4'hB;
      4'h8: inv_map = 4'hC;
      4'h7: inv_map = 4'hD;
      4'hB: inv_map = 4'hE;
      4'h4: inv_map = 4'hF;
      default: inv_map = 4'hx;
    endcase
  endfunction

  // Core functional check (sample after combinational settles via ##0)
  property p_fwd;
    @(data_in or data_out) !$isunknown(data_in) |-> ##0 (data_out === ref_map(data_in));
  endproperty
  assert property (p_fwd)
    else $error("my_logic: mapping mismatch: in=%0h out=%0h exp=%0h",
                data_in, data_out, ref_map(data_in));

  // Inverse consistency (checks bijection)
  property p_inv;
    @(data_in or data_out) !$isunknown(data_out) |-> ##0 (inv_map(data_out) === data_in);
  endproperty
  assert property (p_inv)
    else $error("my_logic: inverse mismatch: out=%0h in=%0h exp_in=%0h",
                data_out, data_in, inv_map(data_out));

  // X-propagation and cleanliness
  property p_known_out_when_known_in;
    @(data_in or data_out) !$isunknown(data_in) |-> ##0 !$isunknown(data_out);
  endproperty
  assert property (p_known_out_when_known_in)
    else $error("my_logic: known input produced X on output: in=%0h out=%0h",
                data_in, data_out);

  property p_x_in_implies_x_out;
    @(data_in or data_out) $isunknown(data_in) |-> ##0 $isunknown(data_out);
  endproperty
  assert property (p_x_in_implies_x_out)
    else $error("my_logic: X/Z input did not produce X on output: in=%0h out=%0h",
                data_in, data_out);

  // Functional coverage for all 16 mappings (input hit with correct output)
  genvar i;
  for (i = 0; i < 16; i++) begin : gen_cov
    localparam logic [3:0] VIN  = logic'(i[3:0]);
    localparam logic [3:0] VOUT = ref_map(VIN);
    cover property (@(data_in or data_out) 1'b1 |-> ##0 (data_in === VIN && data_out === VOUT));
  end

  // Coverage of X behavior (optional but useful)
  cover property (@(data_in or data_out) 1'b1 |-> ##0 ($isunknown(data_in) && $isunknown(data_out)));

endmodule

bind my_logic my_logic_chk u_my_logic_chk(.data_in(data_in), .data_out(data_out));
`endif