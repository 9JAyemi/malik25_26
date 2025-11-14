// SVA checker for gray_to_binary
module gray_to_binary_sva(
  input logic        clk,
  input logic [3:0]  G,
  input logic [3:0]  B
);
  default clocking cb @(posedge clk); endclocking

  function automatic logic [3:0] bin_of_gray (input logic [3:0] g);
    bin_of_gray[3] = g[3];
    bin_of_gray[2] = g[3] ^ g[2];
    bin_of_gray[1] = g[3] ^ g[2] ^ g[1];
    bin_of_gray[0] = g[3] ^ g[2] ^ g[1] ^ g[0];
  endfunction

  function automatic logic [3:0] gray_of_bin (input logic [3:0] b);
    gray_of_bin = b ^ (b >> 1);
  endfunction

  // No X/Z on output when input is known
  assert property (!$isunknown(G) |-> !$isunknown(B))
    else $error("gray_to_binary: B has X/Z while G is known");

  // Functional mapping: B == binary(G)
  assert property (!$isunknown(G) |-> (B == bin_of_gray(G)))
    else $error("gray_to_binary: wrong gray->binary mapping");

  // Round-trip consistency: Gray(B) == G
  assert property (!$isunknown({G,B}) |-> (gray_of_bin(B) == G))
    else $error("gray_to_binary: round-trip mismatch");

  // Determinism: if G stable, B stable
  assert property ($stable(G) |-> $stable(B))
    else $error("gray_to_binary: B changed without G changing");

  // Injectivity: different G implies different B
  assert property (!$isunknown({G,$past(G)}) && (G != $past(G)) |-> (B != $past(B)))
    else $error("gray_to_binary: non-injective mapping");

  // Coverage
  cover property (!$isunknown(G) && (B == bin_of_gray(G))); // functional hit
  generate
    genvar i;
    for (i = 0; i < 16; i++) begin : cov_all_inputs
      cover property (G == i[3:0] && (B == bin_of_gray(G)));
    end
  endgenerate
endmodule

// Bind into DUT (provide a sampling clock from your TB)
bind gray_to_binary gray_to_binary_sva sva (.clk(clk), .G(G), .B(B));