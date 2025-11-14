// SVA for binary_to_gray. Bind this checker to the DUT.

module binary_to_gray_sva(input logic [3:0] A, input logic [3:0] G);

  // Functional equivalence (vector form)
  ap_gray_map: assert property (@(*)
    G == {A[3]^A[2], A[2]^A[1], A[1]^A[0], A[0]}
  );

  // If inputs are known, outputs must be known
  ap_no_x_when_A_known: assert property (@(*)
    !$isunknown(A) |-> !$isunknown(G)
  );

  // If inputs are stable, outputs remain stable
  ap_stable: assert property (@(*)
    $stable(A) |-> $stable(G)
  );

  // Input space coverage (all 16 values exercised with known inputs)
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : gen_cov_all_A
      c_all_A_vals: cover property (@(*)
        !$isunknown(A) && A == i[3:0]
      );
    end
  endgenerate

endmodule

bind binary_to_gray binary_to_gray_sva b2g_sva(.A(A), .G(G));