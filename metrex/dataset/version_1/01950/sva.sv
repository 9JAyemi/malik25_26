// SVA for karnaugh_map
// Concise, full functional check + coverage of all input combinations

module karnaugh_map_sva(input logic A, B, C, D, input logic F);
  localparam logic [15:0] TRUTH = 16'h9965; // 1's at {0,2,5,6,8,11,12,15}
  wire [3:0] idx = {A,B,C,D};

  // Fire assertions/coverage on any input edge
  `define COMB_EV (posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)

  // Inputs must be known (helps catch unintended X/Z that would latch F in the case stmt)
  assert property (@(`COMB_EV) !$isunknown(idx))
    else $error("karnaugh_map: X/Z on inputs A/B/C/D");

  // Output must be known when inputs are known
  assert property (@(`COMB_EV) !$isunknown(idx) |-> !$isunknown(F))
    else $error("karnaugh_map: F is X/Z with known inputs");

  // Golden truth-table check (single concise assertion)
  assert property (@(`COMB_EV) !$isunknown(idx) |-> (F === TRUTH[idx]))
    else $error("karnaugh_map: F != expected for A B C D = %b", idx);

  // Functional coverage: hit all 16 input combinations
  genvar i;
  for (i = 0; i < 16; i++) begin : COV_ALL_COMBOS
    cover property (@(`COMB_EV) (idx == i[3:0]));
  end
endmodule

// Bind to DUT
bind karnaugh_map karnaugh_map_sva sva_inst(.A(A), .B(B), .C(C), .D(D), .F(F));