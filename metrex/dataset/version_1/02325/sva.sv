// SVA checker for karnaugh_map
// Bind this module to the DUT and connect a sampling clock (and optional reset)
module karnaugh_map_sva(
  input logic clk,
  input logic rst_n,          // tie high if unused
  input logic A, B, C, D, E,
  input logic F
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Spec-derived reference function (minimized, not a copy-paste of case table)
  function automatic logic f_ref (logic A,B,C,D,E);
    return ( (!A &&  B && (D || E))         // A' B (D+E)
          || (!A && !B &&  C &&  E)         // A' B' C E
          || (!A && !B && !C && !D && !E)   // 00000
          || ( A && !B && !C &&  D)         // A  B' C' D
          || ( A &&  B &&  C &&  D)         // A  B  C  D
          || ( A &&  B && !C && !D && !E)   // 11000
           );
  endfunction

  // 4-state safety
  ap_inputs_known: assert property (!$isunknown({A,B,C,D,E}));
  ap_F_known:      assert property (!$isunknown(F));

  // Functional equivalence (clocked)
  ap_func: assert property (!$isunknown({A,B,C,D,E}) |-> (F == f_ref(A,B,C,D,E)));

  // Zero-delay combinational check (catches glitches in sim)
  always_comb begin
    if (!$isunknown({A,B,C,D,E})) assert (#0 (F == f_ref(A,B,C,D,E)));
    assert (#0 !$isunknown(F));
  end

  // Compact, targeted functional coverage (hit each prime implicant region)
  cover property (!A &&  B &&  D && !E && F);   // A'B(D|E): D path
  cover property (!A &&  B && !D &&  E && F);   // A'B(D|E): E path
  cover property (!A && !B &&  C &&  E && F);   // A'B'CE
  cover property (!A && !B && !C && !D && !E && F); // 00000
  cover property ( A && !B && !C &&  D && !E && F); // AB'C'D, E=0
  cover property ( A && !B && !C &&  D &&  E && F); // AB'C'D, E=1
  cover property ( A &&  B &&  C &&  D && !E && F); // ABCD,  E=0
  cover property ( A &&  B &&  C &&  D &&  E && F); // ABCD,  E=1
  cover property ( A &&  B && !C && !D && !E && F); // 11000

  // Exhaustive stimulus coverage of all input combinations
  genvar v;
  generate
    for (v = 0; v < 32; v++) begin : COV_ALL_VECS
      cover property ({A,B,C,D,E} == v[4:0]);
    end
  endgenerate

  // Sanity: both output values observed
  cover property ( !$isunknown({A,B,C,D,E}) &&  F );
  cover property ( !$isunknown({A,B,C,D,E}) && !F );

endmodule

// Example bind (adjust clk/rst_n hookups to your environment)
// bind karnaugh_map karnaugh_map_sva u_karnaugh_map_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));