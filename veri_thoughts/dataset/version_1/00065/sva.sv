// SVA checker for top_module
module top_module_sva(
    input  logic [2:0] a,
    input  logic [2:0] b,
    input  logic [2:0] out_or_bitwise,
    input  logic       out_or_logical,
    input  logic [5:0] out_not
);
  // Fire checks on any combinational change
  event comb_ev; always @* -> comb_ev;

  // No X/Z on outputs when inputs are known
  assert property (@(comb_ev) !$isunknown({a,b}) |-> !$isunknown({out_or_bitwise,out_or_logical,out_not}));

  // Functional correctness
  assert property (@(comb_ev) out_or_bitwise == (a | b));
  assert property (@(comb_ev) out_or_logical == ((a != 3'b000) || (b != 3'b000)));
  assert property (@(comb_ev) out_not == {~b, ~a});
  // Cross-consistency between bitwise and logical ORs
  assert property (@(comb_ev) out_or_logical == (|out_or_bitwise));

  // Bit-level checks and coverage
  genvar i;
  generate
    for (i=0; i<3; i++) begin : per_bit
      assert property (@(comb_ev) (a[i]==1'b0 && b[i]==1'b0) |-> out_or_bitwise[i]==1'b0);
      assert property (@(comb_ev) (a[i]==1'b1 ||  b[i]==1'b1) |-> out_or_bitwise[i]==1'b1);
      assert property (@(comb_ev) out_not[i]   == ~a[i]);
      assert property (@(comb_ev) out_not[i+3] == ~b[i]);

      cover  property (@(comb_ev) a[i]==1'b1 && b[i]==1'b0 && out_or_bitwise[i]==1'b1);
      cover  property (@(comb_ev) a[i]==1'b0 && b[i]==1'b1 && out_or_bitwise[i]==1'b1);
    end
  endgenerate

  // Scenario coverage
  cover property (@(comb_ev) a==3'b000 && b==3'b000 && out_or_bitwise==3'b000 && out_or_logical==1'b0);
  cover property (@(comb_ev) a!=3'b000 && b==3'b000 && out_or_logical==1'b1);
  cover property (@(comb_ev) a==3'b000 && b!=3'b000 && out_or_logical==1'b1);
  cover property (@(comb_ev) a!=3'b000 && b!=3'b000 && out_or_logical==1'b1);
  cover property (@(comb_ev) a==3'b111 && b==3'b111 && out_or_bitwise==3'b111 && out_or_logical==1'b1);
endmodule

// Bind into the DUT
bind top_module top_module_sva sva_top_module (.*);