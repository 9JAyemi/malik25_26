// SVA for selector_module
// Bind this to the DUT; no DUT/testbench edits required beyond the bind.

module selector_module_sva
  #(parameter WIDTH = 8)
  (
    input  logic [1:0]         SEL,
    input  logic [WIDTH-1:0]   A,
    input  logic [WIDTH-1:0]   B,
    input  logic [WIDTH-1:0]   OUT
  );

  // Combinational, clockless checking via immediate assertions
  always_comb begin
    // Basic sanity
    assert (!$isunknown(SEL)) else $error("SEL has X/Z");
    if (!(SEL==2'b11 && B==0)) assert (!$isunknown(OUT)) else $error("OUT X/Z when not div-by-zero case");

    // Functional correctness per selection
    unique case (SEL)
      2'b00: begin
        assert (OUT === (A + B)) else $error("SUM mismatch: OUT=%0h A+B=%0h", OUT, (A+B));
      end
      2'b01: begin
        assert (OUT === (A - B)) else $error("DIFF mismatch: OUT=%0h A-B=%0h", OUT, (A-B));
      end
      2'b10: begin
        assert (OUT === (A * B)) else $error("PROD mismatch: OUT=%0h A*B=%0h", OUT, (A*B));
      end
      2'b11: begin
        // Disallow divide-by-zero selection; if it occurs, OUT should be X
        if (B != 0)
          assert (OUT === (A / B)) else $error("QUO mismatch: OUT=%0h A/B=%0h", OUT, (A/B));
        else
          assert ($isunknown(OUT)) else $error("Divide-by-zero selected but OUT not X");
      end
    endcase

    // Functional coverage (immediate cover)
    cover (SEL==2'b00 && OUT === (A+B));
    cover (SEL==2'b01 && OUT === (A-B));
    cover (SEL==2'b10 && OUT === (A*B));
    cover (SEL==2'b11 && B!=0 && OUT === (A/B));

    // Important corner cases
    cover (SEL==2'b00 && ((A + B) < A));                                  // add wrap
    cover (SEL==2'b01 && (A < B));                                         // borrow
    cover (SEL==2'b10 && (A!=0) && (B!=0) && ((A*B) > {WIDTH{1'b1}}));     // mult truncation
    cover (SEL==2'b11 && B!=0 && (A % B)!=0);                              // non-zero remainder
    cover (SEL==2'b11 && B==0);                                            // div-by-zero attempted
  end

endmodule

bind selector_module selector_module_sva
  #(.WIDTH(8)))
  selector_module_sva_i (
    .SEL(SEL),
    .A(A),
    .B(B),
    .OUT(OUT)
  );