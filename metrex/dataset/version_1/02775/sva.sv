// SVA checker for comparator. Bind this to the DUT.

module comparator_sva #(parameter int W=4)
(
  input logic [W-1:0] a,
  input logic [W-1:0] b,
  input logic         gt,
  input logic         lt,
  input logic         eq
);

  // Combinational assertions (immediate) and coverage
  always @* begin
    // Basic legality: exactly one output asserted
    assert ($onehot({gt,lt,eq}))
      else $error("comparator: outputs not onehot gt=%0b lt=%0b eq=%0b", gt,lt,eq);

    // Known-inputs -> known and correct outputs
    if (!$isunknown({a,b})) begin
      assert (!$isunknown({gt,lt,eq}))
        else $error("comparator: X/Z on outputs for known inputs, a=%0h b=%0h", a,b);
      assert (gt == (a > b))
        else $error("comparator: gt mismatch a=%0d b=%0d", a,b);
      assert (lt == (a < b))
        else $error("comparator: lt mismatch a=%0d b=%0d", a,b);
      assert (eq == (a == b))
        else $error("comparator: eq mismatch a=%0d b=%0d", a,b);
    end

    // Functional coverage: all relation outcomes
    cover (a==b && eq && !gt && !lt);
    cover (a>b && gt && !lt && !eq);
    cover (a<b && lt && !gt && !eq);

    // Edge/boundary scenarios
    cover (a==4'h0 && b==4'hF && lt);
    cover (a==4'hF && b==4'h0 && gt);
    cover (a==b+1 && gt);
    cover (b==a+1 && lt);
  end

endmodule

bind comparator comparator_sva #(.W(4)) cmp_sva_i (.a(a), .b(b), .gt(gt), .lt(lt), .eq(eq));