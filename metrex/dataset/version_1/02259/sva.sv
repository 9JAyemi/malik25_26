// SVA for sky130_fd_sc_lp__o41ai
// Y = ~(B1 & (A1|A2|A3|A4))

module sky130_fd_sc_lp__o41ai_sva (
  input logic Y,
  input logic A1, A2, A3, A4, B1,
  input logic or0_out, nand0_out_Y
);

  // Functional correctness (sample on any input change, check after ##0 settle)
  property p_func_eq;
    @(A1 or A2 or A3 or A4 or B1)
      1'b1 |-> ##0 (Y === ~(B1 & (A1 | A2 | A3 | A4)));
  endproperty
  assert property (p_func_eq);

  // Check each stage matches its boolean intent
  property p_or_stage;
    @(A1 or A2 or A3 or A4)
      1'b1 |-> ##0 (or0_out === (A1 | A2 | A3 | A4));
  endproperty
  assert property (p_or_stage);

  property p_nand_stage;
    @(B1 or or0_out)
      1'b1 |-> ##0 (nand0_out_Y === ~(B1 & or0_out));
  endproperty
  assert property (p_nand_stage);

  property p_buf_stage;
    @(nand0_out_Y or Y)
      1'b1 |-> ##0 (Y === nand0_out_Y);
  endproperty
  assert property (p_buf_stage);

  // If all inputs are known 0/1, output must be known
  property p_no_x_on_known_inputs;
    @(A1 or A2 or A3 or A4 or B1)
      (!$isunknown({A1,A2,A3,A4,B1})) |-> ##0 (!$isunknown(Y));
  endproperty
  assert property (p_no_x_on_known_inputs);

  // Minimal functional coverage of key use-cases
  cover property (@(A1 or A2 or A3 or A4 or B1) (B1==1'b0) ##0 (Y==1'b1));
  cover property (@(A1 or A2 or A3 or A4 or B1) (B1==1'b1 && !(A1|A2|A3|A4)) ##0 (Y==1'b1));
  cover property (@(A1 or A2 or A3 or A4 or B1) (B1==1'b1 && (A1|A2|A3|A4)) ##0 (Y==1'b0));

  // Single-hot A coverage when B1=1 (each A alone can drive Y low)
  cover property (@(A1 or A2 or A3 or A4 or B1) (B1 &&  A1 && !A2 && !A3 && !A4) ##0 (Y==0));
  cover property (@(A1 or A2 or A3 or A4 or B1) (B1 && !A1 &&  A2 && !A3 && !A4) ##0 (Y==0));
  cover property (@(A1 or A2 or A3 or A4 or B1) (B1 && !A1 && !A2 &&  A3 && !A4) ##0 (Y==0));
  cover property (@(A1 or A2 or A3 or A4 or B1) (B1 && !A1 && !A2 && !A3 &&  A4) ##0 (Y==0));

  // Extreme case: all As high with B1=1 -> Y=0
  cover property (@(A1 or A2 or A3 or A4 or B1) (B1 && A1 && A2 && A3 && A4) ##0 (Y==0));

endmodule

// Bind into DUT to access internal nets
bind sky130_fd_sc_lp__o41ai sky130_fd_sc_lp__o41ai_sva i_o41ai_sva (
  .Y(Y), .A1(A1), .A2(A2), .A3(A3), .A4(A4), .B1(B1),
  .or0_out(or0_out), .nand0_out_Y(nand0_out_Y)
);