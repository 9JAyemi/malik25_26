// SVA for GDA_St_N8_M8_P1
// Combinational properties sampled @(*), no testbench/DUT changes needed.

module GDA_St_N8_M8_P1_sva (
  input logic [7:0] in1,
  input logic [7:0] in2,
  input logic [8:0] res,
  input logic [7:0] g,   // {g7..g0}
  input logic [7:0] p,   // {p7..p0}
  input logic [8:1] c    // {c8..c1}
);
  default clocking cb @(*); endclocking

  // No-X on outputs and key internal nets when inputs are known
  ap_no_x: assert property ( !$isunknown({in1,in2}) |-> !$isunknown({res,g,p,c}) )
    else $error("X/Z detected on outputs/internals for known inputs");

  // Generate/Propagate correctness
  genvar i;
  generate
    for (i=0; i<8; i++) begin : GP_CHK
      ap_g: assert property ( g[i] == (in1[i] & in2[i]) )
        else $error("g[%0d] wrong", i);
      ap_p: assert property ( p[i] == (in1[i] ^ in2[i]) )
        else $error("p[%0d] wrong", i);
    end
  endgenerate

  // Carry mapping c1..c8 = g0..g7
  generate
    for (i=1; i<=7; i++) begin : C_CHK
      ap_c: assert property ( c[i] == g[i-1] )
        else $error("c[%0d]!=g[%0d]", i, i-1);
    end
  endgenerate
  ap_c8: assert property ( c[8] == g[7] )
    else $error("c8!=g7");

  // Result bit-level functional checks (direct from inputs)
  ap_res0: assert property ( res[0] == (in1[0] ^ in2[0]) )
    else $error("res[0] wrong");

  generate
    for (i=1; i<=6; i++) begin : RES_MID
      ap_resi: assert property ( res[i] == ((in1[i] ^ in2[i]) ^ g[i-1]) )
        else $error("res[%0d] wrong", i);
    end
  endgenerate

  // Top 2 bits: sum of four 1-bit terms (in1[7], in2[7], g6, g7), keep only 2 LSBs
  ap_res78: assert property (
      {res[8],res[7]} == ({1'b0,in1[7]} + {1'b0,in2[7]} + {1'b0,g[6]} + {1'b0,g[7]})
    ) else $error("{res[8:7]} wrong");

  // Full golden check for extra safety (concise formulation)
  function automatic [8:0] golden_res(input logic [7:0] a,b);
    logic [7:0] gg;
    gg = a & b;
    golden_res[0] = a[0] ^ b[0];
    golden_res[1] = (a[1]^b[1]) ^ gg[0];
    golden_res[2] = (a[2]^b[2]) ^ gg[1];
    golden_res[3] = (a[3]^b[3]) ^ gg[2];
    golden_res[4] = (a[4]^b[4]) ^ gg[3];
    golden_res[5] = (a[5]^b[5]) ^ gg[4];
    golden_res[6] = (a[6]^b[6]) ^ gg[5];
    {golden_res[8], golden_res[7]} = {1'b0,a[7]} + {1'b0,b[7]} + {1'b0,gg[6]} + {1'b0,gg[7]};
  endfunction

  ap_res_full: assert property ( res == golden_res(in1,in2) )
    else $error("res mismatch vs golden");

  // Coverage: exercise key features and corner cases
  // - Each propagate high at least once
  generate
    for (i=0; i<8; i++) begin : COV_P
      cp_p_hi: cover property ( p[i] );
    end
  endgenerate
  // - Carry-outs present
  cp_c7:  cover property ( c[7] );
  cp_c8:  cover property ( c[8] );
  // - MSB 2-bit field hits all values
  cp_r00: cover property ( {res[8],res[7]} == 2'b00 );
  cp_r01: cover property ( {res[8],res[7]} == 2'b01 );
  cp_r10: cover property ( {res[8],res[7]} == 2'b10 );
  cp_r11: cover property ( {res[8],res[7]} == 2'b11 );
  // - Extremes
  cp_zeros: cover property ( (in1==8'h00) && (in2==8'h00) );
  cp_ones:  cover property ( (in1==8'hFF) && (in2==8'hFF) );
  // - Double-carry path active
  cp_double_carry: cover property ( g[6] && g[7] );
endmodule

// Bind into the DUT to access internals
bind GDA_St_N8_M8_P1 GDA_St_N8_M8_P1_sva sva (
  .in1(in1),
  .in2(in2),
  .res(res),
  .g({g7,g6,g5,g4,g3,g2,g1,g0}),
  .p({p7,p6,p5,p4,p3,p2,p1,p0}),
  .c({c8,c7,c6,c5,c4,c3,c2,c1})
);