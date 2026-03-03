// SVA checker for mux4to1 (clockless, combinational sampling)
module mux4to1_sva(input logic [1:0] I,
                   input logic [1:0] S,
                   input logic       O);

  // Functional correctness for all fully-known select values
  ap_sel00: assert property (@(I or S or O) (S === 2'b00) |-> (O === I[0]));
  ap_sel01: assert property (@(I or S or O) (S === 2'b01) |-> (O === I[1]));
  ap_sel10: assert property (@(I or S or O) (S === 2'b10) |-> (O === 1'b0));
  ap_sel11: assert property (@(I or S or O) (S === 2'b11) |-> (O === 1'b1));

  // Unknown-propagation sanity: O is never X for constant-driven selects,
  // and only X for data-driven selects if the selected data is X.
  ap_const_no_x0: assert property (@(I or S or O) (S === 2'b10) |-> !$isunknown(O));
  ap_const_no_x1: assert property (@(I or S or O) (S === 2'b11) |-> !$isunknown(O));
  ap_data_no_x0:  assert property (@(I or S or O) (S === 2'b00 && !$isunknown(I[0])) |-> !$isunknown(O));
  ap_data_no_x1:  assert property (@(I or S or O) (S === 2'b01 && !$isunknown(I[1])) |-> !$isunknown(O));

  // Coverage: hit each select value with correct output, and exercise O=0/1/X
  cp_sel00: cover property (@(I or S or O) (S === 2'b00) && (O === I[0]));
  cp_sel01: cover property (@(I or S or O) (S === 2'b01) && (O === I[1]));
  cp_sel10: cover property (@(I or S or O) (S === 2'b10) && (O === 1'b0));
  cp_sel11: cover property (@(I or S or O) (S === 2'b11) && (O === 1'b1));
  cp_o0:    cover property (@(I or S or O) (O === 1'b0));
  cp_o1:    cover property (@(I or S or O) (O === 1'b1));
  cp_ox:    cover property (@(I or S or O) $isunknown(O));

endmodule

// Bind into the DUT (no clock required)
bind mux4to1 mux4to1_sva u_mux4to1_sva (.I(I), .S(S), .O(O));