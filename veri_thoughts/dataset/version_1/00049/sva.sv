// SVA for my_module
// Bind this file to the DUT:  bind my_module my_module_sva sva_i (.*);

module my_module_sva (
  input  logic Y,
  input  logic A1,
  input  logic A2,
  input  logic B1,
  input  logic C1,
  input  logic VPWR,
  input  logic VGND
);

  // Define power-good
  function automatic logic power_good;
    power_good = (VPWR === 1'b1) && (VGND === 1'b0);
  endfunction

  // Main combinational equivalence check (delta-cycle safe)
  // Y should equal ~( (A1 & A2) | ((~B1) | C1) ) when power is good
  always_comb begin
    if (power_good()) begin
      logic exp;
      exp = ~((A1 & A2) | ((~B1) | C1));
      assert #0 (Y === exp)
        else $error("my_module func mismatch: Y=%b exp=%b A1=%b A2=%b B1=%b C1=%b",
                    Y, exp, A1, A2, B1, C1);
      // If all inputs known under power-good, output must be known
      if (!($isunknown({A1,A2,B1,C1})))
        assert #0 (!$isunknown(Y))
          else $error("my_module X-prop: Y unknown with known inputs");
    end
  end

  // Strengthening properties that must always hold under power-good
  // If C1==1 -> Y==0 (dominant 1 at OR input)
  assert property ( power_good() && (C1 === 1'b1) |-> (Y === 1'b0) )
    else $error("C1=1 should force Y=0");

  // If B1==0 -> ~B1==1 -> Y==0
  assert property ( power_good() && (B1 === 1'b0) |-> (Y === 1'b0) )
    else $error("B1=0 should force Y=0");

  // If B1==1 and C1==0 -> Y == ~(A1 & A2)
  assert property ( power_good() && (B1 === 1'b1) && (C1 === 1'b0) |-> (Y === ~(A1 & A2)) )
    else $error("B1=1,C1=0 slice should behave as NOR of A1&A2");

  // Y==1 only when B1==1, C1==0, and (A1&A2)==0
  assert property ( power_good() && (Y === 1'b1) |-> (B1 === 1'b1 && C1 === 1'b0 && !(A1 & A2)) )
    else $error("Y=1 preconditions violated");

  // Y==0 implies at least one OR input is 1
  assert property ( power_good() && (Y === 1'b0) |-> ((A1 & A2) || (~B1) || C1) )
    else $error("Y=0 but no driving term is 1");

  // Basic activity coverage
  cover property ( power_good() );
  cover property ( power_good() && $rose(Y) );
  cover property ( power_good() && $fell(Y) );
  cover property ( power_good() && (Y === 1'b1) );
  cover property ( power_good() && (Y === 1'b0) );

  // Functional input-space coverage (all 16 input combinations under power-good)
  // Vector order: {A1, A2, B1, C1}
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : CMB_COV
      localparam logic [3:0] V = i[3:0];
      cover property ( power_good() && {A1, A2, B1, C1} == V );
    end
  endgenerate

endmodule