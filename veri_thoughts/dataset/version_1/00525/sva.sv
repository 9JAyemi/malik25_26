// SVA checker for bin2gray; bind to DUT as shown at bottom.
module bin2gray_sva(input logic [3:0] B, input logic [3:0] G);

  function automatic logic [3:0] gray(input logic [3:0] b);
    return (b >> 1) ^ b;
  endfunction

  // Any edge on B or G bits
  `define B_EDGES (posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
  `define G_EDGES (posedge G[0] or negedge G[0] or posedge G[1] or negedge G[1] or posedge G[2] or negedge G[2] or posedge G[3] or negedge G[3])

  // Functional correctness (when inputs are known)
  a_func: assert property (@`B_EDGES !$isunknown(B) |-> (G == gray(B)))
    else $error("bin2gray mismatch: B=%0h G=%0h exp=%0h", B, G, gray(B));

  // No unknowns on G when B is known
  a_no_x_out: assert property (@`B_EDGES !$isunknown(B) |-> !$isunknown(G))
    else $error("G has X/Z while B known: B=%0h G=%0h", B, G);

  // No spurious G changes without a B change (glitch check)
  a_no_spurious_g: assert property (@`G_EDGES disable iff ($isunknown(B) || $isunknown(G)) $changed(B))
    else $error("G changed without B change: B=%0h G=%0h", B, G);

  // Coverage: see every input value with correct mapped output
  generate
    genvar v;
    for (v = 0; v < 16; v++) begin: C_VALS
      localparam logic [3:0] VAL = v[3:0];
      localparam logic [3:0] EXP = (VAL >> 1) ^ VAL;
      c_val: cover property (@`B_EDGES (B == VAL) && (G == EXP));
    end
  endgenerate

  // Coverage: each output bit toggles both directions at least once
  generate
    genvar i;
    for (i = 0; i < 4; i++) begin: C_TOG
      c_rise: cover property (@(posedge G[i])) 1;
      c_fall: cover property (@(negedge G[i])) 1;
    end
  endgenerate

  // Coverage: when B increments/decrements by 1, Gray changes by exactly one bit
  c_inc_gray: cover property (@`B_EDGES !$isunknown(B) && !$isunknown($past(B)) &&
                              (B == $past(B)+1) && $onehot(G ^ $past(G)));
  c_dec_gray: cover property (@`B_EDGES !$isunknown(B) && !$isunknown($past(B)) &&
                              (B == $past(B)-1) && $onehot(G ^ $past(G)));

endmodule

bind bin2gray bin2gray_sva u_bin2gray_sva(.B(B), .G(G));