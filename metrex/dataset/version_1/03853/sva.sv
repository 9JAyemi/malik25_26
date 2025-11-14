// SVA for sky130_fd_sc_ls__o221ai
// Function: Y = ~((A1|A2) & (B1|B2) & C1)

module sky130_fd_sc_ls__o221ai_sva (
  input Y, A1, A2, B1, B2, C1,
  input VPWR, VGND, VPB, VNB
);
  // convenience nets
  wire AO = (A1 | A2);
  wire BO = (B1 | B2);

  // Rails must be correct whenever we care about functionality
  property p_rails_ok;
    @(A1 or A2 or B1 or B2 or C1)
      1 |-> ##0 (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0);
  endproperty
  assert property (p_rails_ok);

  // Functional equivalence (when inputs and rails are known)
  property p_truth;
    @(A1 or A2 or B1 or B2 or C1)
      (!$isunknown({A1,A2,B1,B2,C1}) &&
       VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0)
      |-> ##0 (Y === ~(AO & BO & C1));
  endproperty
  assert property (p_truth);

  // Output must not be X when inputs are known and rails are good
  property p_no_x_out;
    @(A1 or A2 or B1 or B2 or C1)
      (!$isunknown({A1,A2,B1,B2,C1}) &&
       VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0)
      |-> ##0 !$isunknown(Y);
  endproperty
  assert property (p_no_x_out);

  // Dominating-value implications (concise corner checks)
  assert property (@(A1 or A2 or B1 or B2 or C1)
                   (C1===1'b0) |-> ##0 (Y===1'b1));
  assert property (@(A1 or A2 or B1 or B2 or C1)
                   (AO===1'b0) |-> ##0 (Y===1'b1));
  assert property (@(A1 or A2 or B1 or B2 or C1)
                   (BO===1'b0) |-> ##0 (Y===1'b1));
  assert property (@(A1 or A2 or B1 or B2 or C1)
                   (C1===1'b1 && AO===1'b1 && BO===1'b1) |-> ##0 (Y===1'b0));

  // Minimal functional coverage
  // Output value coverage
  cover property (@(A1 or A2 or B1 or B2 or C1)
                  (!$isunknown({A1,A2,B1,B2,C1})) ##0 (Y==1'b0));
  cover property (@(A1 or A2 or B1 or B2 or C1)
                  (!$isunknown({A1,A2,B1,B2,C1})) ##0 (Y==1'b1));

  // Corner combinations of factors
  cover property (@(A1 or A2 or B1 or B2 or C1)
                  (C1==1'b1 && AO==1'b1 && BO==1'b1) ##0 (Y==1'b0));
  cover property (@(A1 or A2 or B1 or B2 or C1)
                  (C1==1'b0) ##0 (Y==1'b1));
  cover property (@(A1 or A2 or B1 or B2 or C1)
                  (C1==1'b1 && AO==1'b0 && BO==1'b1) ##0 (Y==1'b1));
  cover property (@(A1 or A2 or B1 or B2 or C1)
                  (C1==1'b1 && AO==1'b1 && BO==1'b0) ##0 (Y==1'b1));

  // Input influence coverage: each input can toggle Y under some condition
  cover property (@(A1) !$isunknown({A1,A2,B1,B2,C1}) ##0 $changed(Y));
  cover property (@(A2) !$isunknown({A1,A2,B1,B2,C1}) ##0 $changed(Y));
  cover property (@(B1) !$isunknown({A1,A2,B1,B2,C1}) ##0 $changed(Y));
  cover property (@(B2) !$isunknown({A1,A2,B1,B2,C1}) ##0 $changed(Y));
  cover property (@(C1) !$isunknown({A1,A2,B1,B2,C1}) ##0 $changed(Y));
endmodule

// Bind into the DUT (use in your testbench or a package)
bind sky130_fd_sc_ls__o221ai sky130_fd_sc_ls__o221ai_sva
  (.Y(Y), .A1(A1), .A2(A2), .B1(B1), .B2(B2), .C1(C1),
   .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB));