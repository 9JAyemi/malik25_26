// SVA bind module for aes
// - Uses a user-supplied clk/rst_n to sample combinational outputs
// - Asserts exact behavior of all branches and key invariants
// - Provides concise branch coverage
//
// Usage:
//   bind aes aes_sva u_aes_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));
module aes_sva(
  input logic clk,
  input logic rst_n,

  // DUT inputs
  input  logic [3:0] addroundkey_data_i,
  input  logic [3:0] addroundkey_data_reg,
  input  logic [3:0] addroundkey_round,
  input  logic [3:0] key_i,
  input  logic [3:0] keysched_new_key_o,
  input  logic [3:0] round,
  input  logic       addroundkey_start_i,
  input  logic       keysched_ready_o,

  // DUT outputs
  input  logic [3:0] keysched_last_key_i,
  input  logic [3:0] keysched_round_i,
  input  logic [3:0] next_addroundkey_data_reg,
  input  logic [3:0] next_addroundkey_round,
  input  logic [3:0] round_data_var,
  input  logic       keysched_start_i,
  input  logic       next_addroundkey_ready_o
);

  // Branch conditions (per DUT's if/else-if chain order)
  logic cond0, cond1, cond2, cond3, none;
  assign cond0 = (round == 4'd0) && addroundkey_start_i;
  assign cond1 = addroundkey_start_i && (round != 4'd0);
  assign cond2 = (addroundkey_round != round) && keysched_ready_o;
  assign cond3 = (addroundkey_round == round) && keysched_ready_o;
  assign none  = !(cond0 || cond1 || cond2 || cond3);

  // Helper: default last_key selection
  function logic [3:0] def_last_key(input logic [3:0] r);
    return ((r == 4'd0) || (r == 4'd1)) ? key_i : keysched_new_key_o;
  endfunction

  // Sanity: no X/Z on outputs at sample time
  assert property (@(posedge clk) disable iff (!rst_n)
    !$isunknown({keysched_last_key_i, keysched_round_i, next_addroundkey_data_reg,
                 next_addroundkey_round, round_data_var, keysched_start_i,
                 next_addroundkey_ready_o}))
    else $error("aes outputs contain X/Z");

  // Global invariants
  assert property (@(posedge clk) disable iff (!rst_n)
    round_data_var == next_addroundkey_data_reg)
    else $error("round_data_var must mirror next_addroundkey_data_reg");

  assert property (@(posedge clk) disable iff (!rst_n)
    keysched_start_i |-> (keysched_round_i == next_addroundkey_round))
    else $error("keysched_round_i must equal next_addroundkey_round when starting");

  assert property (@(posedge clk) disable iff (!rst_n)
    next_addroundkey_ready_o |-> !keysched_start_i)
    else $error("ready and start must not assert together");

  assert property (@(posedge clk) disable iff (!rst_n)
    next_addroundkey_ready_o |-> (cond0 || cond3))
    else $error("ready may only assert in cond0 or cond3 branches");

  assert property (@(posedge clk) disable iff (!rst_n)
    keysched_start_i |-> (cond1 || cond2))
    else $error("start may only assert in cond1 or cond2 branches");

  // Branch 0: round == 0 && start
  assert property (@(posedge clk) disable iff (!rst_n)
    cond0 |-> ( next_addroundkey_ready_o
                && (next_addroundkey_data_reg == (addroundkey_data_i ^ key_i))
                && (next_addroundkey_round == addroundkey_round)
                && (keysched_start_i == 1'b0)
                && (keysched_round_i == addroundkey_round)
                && (keysched_last_key_i == def_last_key(addroundkey_round)) ))
    else $error("cond0 behavior mismatch");

  // Branch 1: start && round != 0 (and not cond0)
  assert property (@(posedge clk) disable iff (!rst_n)
    (cond1 && !cond0) |-> ( keysched_start_i
                            && (keysched_round_i == 4'd1)
                            && (next_addroundkey_round == 4'd1)
                            && (next_addroundkey_ready_o == 1'b0)
                            && (next_addroundkey_data_reg == addroundkey_data_reg)
                            && (keysched_last_key_i == key_i) ))
    else $error("cond1 behavior mismatch");

  // Branch 2: advance rounds when ready (and not cond0/cond1)
  assert property (@(posedge clk) disable iff (!rst_n)
    (cond2 && !cond0 && !cond1) |-> (
       keysched_start_i
       && (next_addroundkey_round == (addroundkey_round + 4'd1))
       && (keysched_round_i     == (addroundkey_round + 4'd1))
       && (next_addroundkey_ready_o == 1'b0)
       && (next_addroundkey_data_reg == addroundkey_data_reg)
       && (keysched_last_key_i == keysched_new_key_o) ))
    else $error("cond2 behavior mismatch");

  // Branch 3: final addroundkey when ready (and not earlier branches)
  assert property (@(posedge clk) disable iff (!rst_n)
    (cond3 && !cond0 && !cond1 && !cond2) |-> (
       next_addroundkey_ready_o
       && (next_addroundkey_data_reg == (addroundkey_data_i ^ keysched_new_key_o))
       && (next_addroundkey_round == 4'd0)
       && (keysched_start_i == 1'b0)
       && (keysched_round_i == addroundkey_round)
       && (keysched_last_key_i == def_last_key(addroundkey_round)) ))
    else $error("cond3 behavior mismatch");

  // Default path: no branch taken
  assert property (@(posedge clk) disable iff (!rst_n)
    none |-> ( (keysched_start_i == 1'b0)
               && (keysched_round_i == addroundkey_round)
               && (next_addroundkey_data_reg == addroundkey_data_reg)
               && (next_addroundkey_ready_o == 1'b0)
               && (next_addroundkey_round == addroundkey_round)
               && (keysched_last_key_i == def_last_key(addroundkey_round)) ))
    else $error("default behavior mismatch");

  // Concise functional covers (each branch + a typical flow)
  cover property (@(posedge clk) disable iff (!rst_n) cond0);
  cover property (@(posedge clk) disable iff (!rst_n) cond1);
  cover property (@(posedge clk) disable iff (!rst_n) cond2);
  cover property (@(posedge clk) disable iff (!rst_n) cond3);

  // Typical multi-cycle flow: nonzero start -> advance -> final
  cover property (@(posedge clk) disable iff (!rst_n)
    cond1 ##1 cond2 ##1 cond3);

endmodule