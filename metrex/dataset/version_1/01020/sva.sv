// SVA for mux5: concise, high-quality checks and coverage.
// Bind this to the DUT to verify combinational correctness, X-propagation, and select coverage.

module mux5_sva #(parameter WIREWIDTH = 1)(
  input  logic [2:0]             s,
  input  logic [WIREWIDTH:0]     d0, d1, d2, d3, d4,
  input  logic [WIREWIDTH:0]     o
);

  // Combinational equivalence: o must always reflect the selected input
  always_comb begin
    assert #0 (
      o === (s==3'd0 ? d0 :
             s==3'd1 ? d1 :
             s==3'd2 ? d2 :
             s==3'd3 ? d3 : d4)
    ) else $error("mux5 mismatch: s=%0d o=%0h d0=%0h d1=%0h d2=%0h d3=%0h d4=%0h", s, o, d0, d1, d2, d3, d4);
  end

  // X/Z checks: flag unknown select; ensure selected data is known; ensure o is known when inputs are known
  always_comb begin
    assert #0 (!$isunknown(s)) else $error("mux5 select has X/Z: %b", s);

    unique case (s)
      3'd0: assert #0 (!$isunknown(d0)) else $error("mux5 d0 X/Z when selected");
      3'd1: assert #0 (!$isunknown(d1)) else $error("mux5 d1 X/Z when selected");
      3'd2: assert #0 (!$isunknown(d2)) else $error("mux5 d2 X/Z when selected");
      3'd3: assert #0 (!$isunknown(d3)) else $error("mux5 d3 X/Z when selected");
      default: assert #0 (!$isunknown(d4)) else $error("mux5 d4 X/Z when selected (default)");
    endcase

    if (!$isunknown(s)) begin
      case (s)
        3'd0: if (!$isunknown(d0)) assert #0 (!$isunknown(o)) else $error("mux5 o X/Z with valid d0");
        3'd1: if (!$isunknown(d1)) assert #0 (!$isunknown(o)) else $error("mux5 o X/Z with valid d1");
        3'd2: if (!$isunknown(d2)) assert #0 (!$isunknown(o)) else $error("mux5 o X/Z with valid d2");
        3'd3: if (!$isunknown(d3)) assert #0 (!$isunknown(o)) else $error("mux5 o X/Z with valid d3");
        default: if (!$isunknown(d4)) assert #0 (!$isunknown(o)) else $error("mux5 o X/Z with valid d4");
      endcase
    end
  end

  // Functional coverage: exercise each select value and confirm routing
  always_comb begin
    // Hit every select value
    cover (s==3'd0); cover (s==3'd1); cover (s==3'd2); cover (s==3'd3);
    cover (s==3'd4); cover (s==3'd5); cover (s==3'd6); cover (s==3'd7);

    // Hit correct routing for each select
    cover (s==3'd0 && o===d0);
    cover (s==3'd1 && o===d1);
    cover (s==3'd2 && o===d2);
    cover (s==3'd3 && o===d3);
    cover (s==3'd4 && o===d4);
    cover (s==3'd5 && o===d4);
    cover (s==3'd6 && o===d4);
    cover (s==3'd7 && o===d4);
  end

endmodule

// Bind to the DUT
bind mux5 mux5_sva #(.WIREWIDTH(WIREWIDTH)) mux5_sva_i (.*);