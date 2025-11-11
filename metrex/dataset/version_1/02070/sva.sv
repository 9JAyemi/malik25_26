// SVA for rs_fe1_pre_dec
// Bind this module to the DUT to check combinational correctness and cover behavior.

module rs_fe1_pre_dec_sva (
  input logic [13:0] addr_i,
  input logic        pre_dec_o,
  input logic        pre_dec_err_o
);

  // Sample on any addr_i change; use ##0 to evaluate after combinational settles
  // Helper predicates
  function automatic bit f_in_1_7 (logic [3:0] s); return s inside {[4'h1:4'h7]}; endfunction
  function automatic bit f_is_legal_0_8_A (logic [3:0] s); return s inside {4'h0,4'h8,4'hA}; endfunction
  function automatic bit f_is_legal (logic [3:0] s); return f_in_1_7(s) || f_is_legal_0_8_A(s); endfunction

  // Outputs are known (no X/Z) after any addr change
  assert property (@(addr_i) ##0 !$isunknown({pre_dec_o, pre_dec_err_o}))
    else $error("X/Z detected on outputs");

  // Functional correctness: exact Boolean mapping from addr_i[5:2]
  assert property (@(addr_i) 1'b1 |-> ##0 (pre_dec_o      == f_in_1_7(addr_i[5:2])))
    else $error("pre_dec_o mismatch for addr_i[5:2]=%0h", addr_i[5:2]);

  assert property (@(addr_i) 1'b1 |-> ##0 (pre_dec_err_o  == !f_is_legal(addr_i[5:2])))
    else $error("pre_dec_err_o mismatch for addr_i[5:2]=%0h", addr_i[5:2]);

  // If error is asserted, pre_dec must be 0
  assert property (@(addr_i) pre_dec_err_o |-> ##0 !pre_dec_o)
    else $error("pre_dec_o must be 0 when pre_dec_err_o=1");

  // Insensitivity to addr bits outside [5:2]
  assert property (@(addr_i) $stable(addr_i[5:2]) |-> ##0 $stable({pre_dec_o, pre_dec_err_o}))
    else $error("Outputs changed while addr_i[5:2] was stable");

  // Targeted coverage for each behavior class
  cover property (@(addr_i) f_in_1_7(addr_i[5:2]) ##0 (pre_dec_o && !pre_dec_err_o));
  cover property (@(addr_i) f_is_legal_0_8_A(addr_i[5:2]) ##0 (!pre_dec_o && !pre_dec_err_o));
  cover property (@(addr_i) !f_is_legal(addr_i[5:2]) ##0 (pre_dec_err_o && !pre_dec_o));

  // Full value coverage of the decoded field
  covergroup cg_sel @(addr_i);
    coverpoint addr_i[5:2] { bins all_vals[] = {[4'h0:4'hF]}; }
    coverpoint pre_dec_o;
    coverpoint pre_dec_err_o;
  endgroup
  cg_sel cg_sel_i = new();

endmodule

// Bind into the DUT
bind rs_fe1_pre_dec rs_fe1_pre_dec_sva i_rs_fe1_pre_dec_sva (
  .addr_i(addr_i),
  .pre_dec_o(pre_dec_o),
  .pre_dec_err_o(pre_dec_err_o)
);