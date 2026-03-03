// SVA for sky130_fd_sc_hd__nor4b
module sky130_fd_sc_hd__nor4b_sva (
  input logic A, B, C, D_N,
  input logic Y,
  input logic not0_out, nor0_out_Y, // internal nets
  input logic VPWR, VGND, VPB, VNB  // supplies
);

  function automatic logic expY (logic A, B, C, D_N);
    return (~A & ~B & ~C & D_N);
  endfunction

  // Functional equivalence
  property p_func;
    @(A or B or C or D_N or Y) 1 |-> (Y === expY(A,B,C,D_N));
  endproperty
  assert property (p_func);

  // Internal structure checks
  assert property (@(D_N or not0_out) not0_out   === ~D_N);
  assert property (@(A or B or C or not0_out or nor0_out_Y)
                   nor0_out_Y === ~(A | B | C | not0_out));
  assert property (@(nor0_out_Y or Y) Y === nor0_out_Y);

  // No X on Y when inputs are known
  assert property (@(A or B or C or D_N or Y)
                   (!$isunknown({A,B,C,D_N})) |-> (!$isunknown(Y)));

  // Y only changes if at least one input changed
  assert property (@(posedge Y or negedge Y) $changed({A,B,C,D_N}));

  // Power rail sanity (if accessible)
  assert property (@(VPWR or VGND or VPB or VNB)
                   (VPWR === 1'b1 && VPB === 1'b1 && VGND === 1'b0 && VNB === 1'b0));

  // Truth-table coverage (all 16 input combinations observed with correct Y)
  genvar gi;
  generate
    for (gi = 0; gi < 16; gi++) begin : g_cov
      localparam logic [3:0] V = logic'(gi[3:0]);
      cover property (@(A or B or C or D_N or Y)
                      ({A,B,C,D_N} === V) && (Y === expY(A,B,C,D_N)));
    end
  endgenerate

endmodule

bind sky130_fd_sc_hd__nor4b sky130_fd_sc_hd__nor4b_sva sva_i (.*);