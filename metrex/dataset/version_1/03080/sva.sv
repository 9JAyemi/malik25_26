// SVA for nand4bb
module nand4bb_sva (
  input  logic A_N, B_N, C, D,
  input  logic Y,
  input  logic VPB, VPWR, VGND, VNB,
  input  logic AB_N, CD_N, Y_N
);

  wire power_good = (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);

  // Combinational correctness (internal and final function)
  always @* if (power_good) begin
    assert (AB_N === ~(A_N & B_N))              else $error("AB_N != ~(A_N & B_N)");
    assert (CD_N === ~(C & D))                  else $error("CD_N != ~(C & D)");
    assert (Y_N  === ~(AB_N & CD_N))            else $error("Y_N != ~(AB_N & CD_N)");
    assert (Y === Y_N)                          else $error("Y != Y_N");
    assert (Y === ((A_N & B_N) | (C & D)))      else $error("Y != (A_N&B_N)|(C&D)");
  end

  // Output must be known when inputs are known (under good power)
  assert property (@(A_N or B_N or C or D or VPWR or VGND or VPB or VNB)
                   power_good && !$isunknown({A_N,B_N,C,D}) |-> !$isunknown(Y));

  // Dominating cases
  assert property (@(C or D) power_good && (C===1'b1) && (D===1'b1) |-> Y==1'b1);
  assert property (@(A_N or B_N) power_good && (A_N===1'b1) && (B_N===1'b1) |-> Y==1'b1);
  assert property (@(A_N or B_N or C or D)
                   power_good && ((A_N===1'b0 || B_N===1'b0) && (C===1'b0 || D===1'b0)) |-> Y==1'b0);

  // Y only toggles in response to input changes (under good power)
  assert property (@(posedge Y or negedge Y) power_good |-> $changed({A_N,B_N,C,D}));

  // Coverage: Y toggles
  cover property (@(A_N or B_N or C or D) power_good && $rose(Y));
  cover property (@(A_N or B_N or C or D) power_good && $fell(Y));

  // Coverage: all input combinations and mapping to Y
  covergroup cg_inputs @(A_N or B_N or C or D);
    option.per_instance = 1;
    cp_inputs: coverpoint {A_N,B_N,C,D} iff (power_good && !$isunknown({A_N,B_N,C,D})) {
      bins all[] = {[0:15]};
    }
    cp_y: coverpoint Y iff (power_good && !$isunknown({A_N,B_N,C,D})) { bins z = {0}; bins o = {1}; }
    x_in_y: cross cp_inputs, cp_y;
  endgroup
  cg_inputs cg = new();

endmodule

bind nand4bb nand4bb_sva u_nand4bb_sva (.*);