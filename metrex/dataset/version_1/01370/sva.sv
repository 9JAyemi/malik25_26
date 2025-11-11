// SVA for sky130_fd_sc_ls__and4
// Focused, high-quality checks and coverage

module sky130_fd_sc_ls__and4_sva_bind (
  input logic A, B, C, D,
  input logic X,
  input logic VPWR, VGND, VPB, VNB,
  input logic and0_out_X
);
  // Sample on any edge of inputs, output, or internal net
  default clocking cb
    @(posedge A or negedge A or
      posedge B or negedge B or
      posedge C or negedge C or
      posedge D or negedge D or
      posedge X or negedge X or
      posedge and0_out_X or negedge and0_out_X);
  endclocking

  // Power pins sanity (constant supplies)
  initial begin
    assert (VPWR === 1'b1);
    assert (VGND === 1'b0);
    assert (VPB  === 1'b1);
    assert (VNB  === 1'b0);
  end

  // Functional correctness when inputs are known; output must be known and match A&B&C&D
  property p_and4_func_known;
    !$isunknown({A,B,C,D}) |->
      (! $isunknown(X)) && (X === (A & B & C & D));
  endproperty
  assert property (p_and4_func_known);

  // Buffer correctness: internal and output must match whenever the internal is known
  property p_buf_transparent;
    !$isunknown(and0_out_X) |->
      (! $isunknown(X)) && (X === and0_out_X);
  endproperty
  assert property (p_buf_transparent);

  // Minimal coverage:
  // - Each input and output toggles
  cover property ($rose(A)); cover property ($fell(A));
  cover property ($rose(B)); cover property ($fell(B));
  cover property ($rose(C)); cover property ($fell(C));
  cover property ($rose(D)); cover property ($fell(D));
  cover property ($rose(X)); cover property ($fell(X));

  // - Output low and high under canonical conditions
  cover property ((!$isunknown({A,B,C,D})) && (&{A,B,C,D}) && (X==1));
  cover property ((!$isunknown({A,B,C,D})) && (|(~{A,B,C,D})) && (X==0));

  // - All 16 input combinations observed
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : gen_all_input_combos
      cover property ({A,B,C,D} == i[3:0]);
    end
  endgenerate
endmodule

// Bind into the DUT, including the internal net
bind sky130_fd_sc_ls__and4 sky130_fd_sc_ls__and4_sva_bind
  (.A(A), .B(B), .C(C), .D(D),
   .X(X),
   .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB),
   .and0_out_X(and0_out_X));