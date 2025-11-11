// SVA/IC assertions and coverage for the given DUTs.
// Bind these modules to the DUTs as shown at the end.

// Assertions for adder
module adder_sva();
  logic [8:0] ext9;
  always_comb begin
    ext9 = {1'b0,a} + {1'b0,b};

    // Functional correctness
    assert (s == ext9[7:0]) else $error("adder: s != a+b (8b)");
    assert (overflow == ((a[7]==b[7]) && (s[7]!=a[7])))
      else $error("adder: overflow incorrect");

    // Internal implementation sanity (catches width/concatenation bugs)
    assert (sum == ext9) else $error("adder: internal sum != a+b (9b)");
    assert (carry == ext9[8]) else $error("adder: internal carry != add carry");

    // Clean outputs when inputs are known
    if (!$isunknown({a,b})) assert (!$isunknown({s,overflow}))
      else $error("adder: X/Z on outputs");

    // Key coverage
    cover (a==8'h00 && b==8'h00);
    cover (a==8'hFF && b==8'h01);            // wraparound
    cover (a[7]==0 && b[7]==0 && overflow);   // positive overflow
    cover (a[7]==1 && b[7]==1 && overflow);   // negative overflow
    cover (s==8'h00);
    cover (s==8'hFF);
  end
endmodule

// Assertions for xor_module
module xor_module_sva();
  always_comb begin
    assert (out == (in ^ 8'hAA)) else $error("xor_module: out != in ^ 0xAA");
    if (!$isunknown(in)) assert (!$isunknown(out))
      else $error("xor_module: X/Z on out");
    // Coverage
    cover (in==8'h00);
    cover (in==8'hFF);
    cover (out==8'hAA);
    cover (out==8'h55);
  end
endmodule

// Assertions for top_module (end-to-end and connectivity)
module top_module_sva();
  logic [8:0] ext9;
  always_comb begin
    ext9 = {1'b0,a} + {1'b0,b};

    // End-to-end functionality
    assert (s   == ext9[7:0])           else $error("top: s != a+b (8b)");
    assert (out == (ext9[7:0] ^ 8'hAA)) else $error("top: out != (a+b)^0xAA");
    assert (overflow == ((a[7]==b[7]) && (ext9[7]!=a[7])))
      else $error("top: overflow incorrect");

    // Structural connectivity
    assert (out == (s ^ 8'hAA)) else $error("top: out != s ^ 0xAA");

    // Clean outputs when inputs are known
    if (!$isunknown({a,b})) assert (!$isunknown({s,out,overflow}))
      else $error("top: X/Z on outputs");

    // Key coverage
    cover (overflow);
    cover (a==8'h7F && b==8'h01);  // pos overflow exemplar
    cover (a==8'h80 && b==8'h80);  // neg overflow exemplar
    cover (out==8'h00);
    cover (out==8'hFF);
  end
endmodule

// Bind the SVA modules to the DUTs
bind adder      adder_sva   adder_sva_i();
bind xor_module xor_module_sva xor_module_sva_i();
bind top_module top_module_sva top_module_sva_i();