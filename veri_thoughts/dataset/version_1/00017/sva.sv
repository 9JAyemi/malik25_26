// SVA bind file for section2_schematic
// Checks gate-level equivalence, output functions, X-propagation, and covers all input minterms.

module section2_schematic_sva (
  input logic n63, Z_B, n62,
  input logic Len_int, Ren_int,
  input logic Ldir_int, Rdir_int,
  input logic N_1, N_3, N_4, N_8
);

  // Combinational equivalence of internal nets
  always_comb begin
    assert (N_1 == (n63 & Z_B)) else $error("N_1 mismatch");
    assert (N_3 == (Z_B & n62)) else $error("N_3 mismatch");
    assert (N_8 == (~Z_B))     else $error("N_8 mismatch");
    assert (Ldir_int == (~n63)) else $error("Ldir_int mismatch");
    assert (Rdir_int == (~n62)) else $error("Rdir_int mismatch");
    assert (N_4 == (Ldir_int & N_8 & Rdir_int)) else $error("N_4 mismatch");

    // Output equivalence to internal cones
    assert (Len_int == (N_1 | N_4)) else $error("Len_int cone mismatch");
    assert (Ren_int == (N_4 | N_3)) else $error("Ren_int cone mismatch");

    // Output equivalence directly to primary inputs (redundant cross-check)
    assert (Len_int == ((n63 & Z_B) | ((~n63) & (~Z_B) & (~n62))))
      else $error("Len_int func mismatch");
    assert (Ren_int == (((~n63) & (~Z_B) & (~n62)) | (Z_B & n62)))
      else $error("Ren_int func mismatch");

    // X-propagation: if inputs are known, everything must be known
    if (!$isunknown({n63,Z_B,n62})) begin
      assert (!$isunknown({Ldir_int,Rdir_int,N_8,N_1,N_3,N_4,Len_int,Ren_int}))
        else $error("Unknown on internal/output with known inputs");
    end
  end

  // Minimal coverage: all input minterms, output states, and path activations
  always_comb begin
    // 8 input combinations
    cover (n63===0 && Z_B===0 && n62===0);
    cover (n63===0 && Z_B===0 && n62===1);
    cover (n63===0 && Z_B===1 && n62===0);
    cover (n63===0 && Z_B===1 && n62===1);
    cover (n63===1 && Z_B===0 && n62===0);
    cover (n63===1 && Z_B===0 && n62===1);
    cover (n63===1 && Z_B===1 && n62===0);
    cover (n63===1 && Z_B===1 && n62===1);

    // Output states
    cover ( Len_int &&  Ren_int);
    cover ( Len_int && !Ren_int);
    cover (!Len_int &&  Ren_int);
    cover (!Len_int && !Ren_int);

    // Individual path activations
    cover (N_1);
    cover (N_3);
    cover (N_4);
  end

endmodule

bind section2_schematic section2_schematic_sva sva_i (
  .n63(n63), .Z_B(Z_B), .n62(n62),
  .Len_int(Len_int), .Ren_int(Ren_int),
  .Ldir_int(Ldir_int), .Rdir_int(Rdir_int),
  .N_1(N_1), .N_3(N_3), .N_4(N_4), .N_8(N_8)
);