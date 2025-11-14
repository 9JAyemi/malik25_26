// SVA/checkers for priority_mux_addsub and its submodules.
// Bind these into the DUT; no clock required (purely combinational).

// Checker for priority_encoder
module priority_encoder_sva;
  // Bound into priority_encoder scope; can see in,out
  always @* begin
    // Functional equivalence: this encoder is identity mapping
    assert (out === in)
      else $error("priority_encoder: out(%b) != in(%b)", out, in);

    // Knownness: if inputs known, output must be known
    if (!$isunknown(in)) begin
      assert (!$isunknown(out))
        else $error("priority_encoder: out X/Z for in=%b", in);
    end
  end

  // Coverage: all input codes seen
  always @* begin
    cover (in == 2'b00);
    cover (in == 2'b01);
    cover (in == 2'b10);
    cover (in == 2'b11);
  end
endmodule

// Checker for mux_4to1
module mux_4to1_sva;
  // Bound into mux_4to1 scope; can see in0..in3, sel, out
  always @* begin
    if (!$isunknown(sel)) begin
      unique case (sel)
        2'b00: assert (out === in0)
                 else $error("mux_4to1: sel=00 out(%h)!=in0(%h)", out, in0);
        2'b01: assert (out === in1)
                 else $error("mux_4to1: sel=01 out(%h)!=in1(%h)", out, in1);
        2'b10: assert (out === in2)
                 else $error("mux_4to1: sel=10 out(%h)!=in2(%h)", out, in2);
        2'b11: assert (out === in3)
                 else $error("mux_4to1: sel=11 out(%h)!=in3(%h)", out, in3);
      endcase
    end

    // Knownness: if selected input is known, out must be known
    unique case (sel)
      2'b00: if (!$isunknown(in0)) assert(!$isunknown(out))
               else $error("mux_4to1: out X/Z with sel=00 and known in0");
      2'b01: if (!$isunknown(in1)) assert(!$isunknown(out))
               else $error("mux_4to1: out X/Z with sel=01 and known in1");
      2'b10: if (!$isunknown(in2)) assert(!$isunknown(out))
               else $error("mux_4to1: out X/Z with sel=10 and known in2");
      2'b11: if (!$isunknown(in3)) assert(!$isunknown(out))
               else $error("mux_4to1: out X/Z with sel=11 and known in3");
      default: /* sel unknown */ ;
    endcase
  end

  // Coverage: each select hit
  always @* begin
    cover (sel == 2'b00);
    cover (sel == 2'b01);
    cover (sel == 2'b10);
    cover (sel == 2'b11);
  end
endmodule

// Checker for addsub_4bit
module addsub_4bit_sva;
  // Bound into addsub_4bit scope; can see A,B,SUB,out
  always @* begin
    automatic logic [4:0] sum5  = {1'b0,A} + {1'b0,B};
    automatic logic [4:0] diff5 = {1'b0,A} - {1'b0,B};

    assert (SUB ? (out === diff5[3:0]) : (out === sum5[3:0]))
      else $error("addsub_4bit: out(%h) != %s result A(%h) B(%h)",
                  out, (SUB?"A-B":"A+B"), A, B);

    if (!$isunknown({A,B,SUB})) begin
      assert (!$isunknown(out))
        else $error("addsub_4bit: out X/Z with known inputs A=%h B=%h SUB=%b", A, B, SUB);
    end
  end

  // Coverage: op modes and overflow/borrow
  always @* begin
    automatic logic [4:0] sum5  = {1'b0,A} + {1'b0,B};
    cover (!SUB);
    cover ( SUB);
    cover (sum5[4]);                 // addition carry-out (wrap)
    cover (SUB && (A < B));          // subtraction borrow (wrap)
    cover (A==4'h0); cover (A==4'hF);
    cover (B==4'h0); cover (B==4'hF);
  end
endmodule

// Checker for top-level composition
module priority_mux_addsub_sva;
  // Bound into priority_mux_addsub; can see A..D,S,SUB, sel, mux_out, addsub_out, out
  always @* begin
    // Priority encoder identity
    assert (sel === S)
      else $error("top: sel(%b) != S(%b)", sel, S);

    // Mux function
    if (!$isunknown(sel)) begin
      unique case (sel)
        2'b00: assert (mux_out === A) else $error("top mux_out(%h)!=A(%h) sel=00", mux_out, A);
        2'b01: assert (mux_out === B) else $error("top mux_out(%h)!=B(%h) sel=01", mux_out, B);
        2'b10: assert (mux_out === C) else $error("top mux_out(%h)!=C(%h) sel=10", mux_out, C);
        2'b11: assert (mux_out === D) else $error("top mux_out(%h)!=D(%h) sel=11", mux_out, D);
      endcase
    end

    // Add/Sub function
    automatic logic [4:0] sum5  = {1'b0,A} + {1'b0,mux_out};
    automatic logic [4:0] diff5 = {1'b0,A} - {1'b0,mux_out};
    assert (SUB ? (addsub_out === diff5[3:0]) : (addsub_out === sum5[3:0]))
      else $error("top addsub_out(%h) != %s with A=%h M=%h",
                  addsub_out, (SUB?"A-M":"A+M"), A, mux_out);

    // Final assignment
    assert (out === addsub_out)
      else $error("top: out(%h) != addsub_out(%h)", out, addsub_out);

    // Direct end-to-end equivalence
    assert (out === (SUB ? diff5[3:0] : sum5[3:0]))
      else $error("top: out(%h) != end-to-end result", out);

    // Knownness end-to-end
    if (!$isunknown({A,B,C,D,S,SUB})) begin
      assert (!$isunknown({sel,mux_out,addsub_out,out}))
        else $error("top: X/Z observed with fully known inputs");
    end
  end

  // Concise coverage: select x op-mode, and wrap conditions
  always @* begin
    cover (S==2'b00); cover (S==2'b01); cover (S==2'b10); cover (S==2'b11);
    cover (!SUB); cover (SUB);
    cover (!SUB && ({1'b0,A}+{1'b0,mux_out})[4]); // add carry/wrap
    cover ( SUB && (A < mux_out));                // sub borrow/wrap
    cover (A==4'h0); cover (A==4'hF);
    cover (mux_out==4'h0); cover (mux_out==4'hF);
  end
endmodule

// Bind the checkers
bind priority_encoder       priority_encoder_sva pe_chk();
bind mux_4to1               mux_4to1_sva         mux_chk();
bind addsub_4bit            addsub_4bit_sva      addsub_chk();
bind priority_mux_addsub    priority_mux_addsub_sva top_chk();