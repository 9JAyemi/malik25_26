// SVA for bin2gray
// Non-intrusive bind; concurrent checks use @(*) for combinational sampling

module bin2gray_sva (
  input logic [3:0] in,
  input logic [3:0] out
);
  default clocking cb @(*); endclocking

  function automatic logic [3:0] gray_of (logic [3:0] b);
    return {b[3], b[3]^b[2], b[2]^b[1], b[1]^b[0]};
  endfunction

  // Functional equivalence (4-state aware)
  a_eq:           assert property (out === gray_of(in));

  // No X/Z leakage when inputs are clean
  a_no_x_leak:    assert property (!$isunknown(in) |-> !$isunknown(out));

  // Purely combinational causality: out only changes if in changes
  a_change_cause: assert property ($changed(out) |-> $changed(in));

  // Stability: if inputs stable, outputs remain stable
  a_stable:       assert property ($stable(in) |-> $stable(out));

  // Coverage: hit all 16 input values and corresponding expected outputs
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : COV_ALL
      localparam logic [3:0] BIN = i[3:0];
      localparam logic [3:0] GRY = {BIN[3], BIN[3]^BIN[2], BIN[2]^BIN[1], BIN[1]^BIN[0]};
      c_map: cover property (in == BIN && out === GRY);
    end
  endgenerate
endmodule

bind bin2gray bin2gray_sva b2g_sva (.in(in), .out(out));