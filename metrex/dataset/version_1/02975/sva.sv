// SVA for imuldiv_IntMulVariable and submodules.
// Bind these modules into the DUT; concise, focused on key correctness and coverage.

//////////////////////////////////////////////
// Top-level connectivity / handshake SVA  //
//////////////////////////////////////////////
module imuldiv_IntMulVariable_sva
(
  input clk,
  input reset,
  input  [31:0] mulreq_msg_a,
  input  [31:0] mulreq_msg_b,
  input         mulreq_val,
  output        mulreq_rdy,
  output [31:0] mulresp_msg_result,
  output        mulresp_val,
  input         mulresp_rdy
);
  // Access internal wire dpath_out for structural check
  wire [63:0] dpath_out;
  // synthesis translate_off
  // The bind context connects to the target’s internal nets by name
  // Assertions use hierarchical connection through bind (.*)
  default clocking @(posedge clk); endclocking
  default disable iff (reset);

  // Structural mapping: result equals low half of dpath_out
  assert property (mulresp_msg_result == dpath_out[31:0]);

  // Response must remain asserted and data stable until accepted
  assert property (mulresp_val && !mulresp_rdy |=> mulresp_val && $stable(mulresp_msg_result));

  // No X on top-level handshakes
  assert property (!$isunknown({mulreq_rdy,mulresp_val}));

  // Cover: backpressure on response holds value and data
  cover property (mulresp_val && !mulresp_rdy ##1 mulresp_val && !mulresp_rdy ##1 mulresp_val && mulresp_rdy);

  // Cover: a signed and an unsigned multiply requested
  cover property (mulreq_val && mulreq_rdy && (mulreq_msg_a[31]^mulreq_msg_b[31])==0);
  cover property (mulreq_val && mulreq_rdy && (mulreq_msg_a[31]^mulreq_msg_b[31])==1);
  // synthesis translate_on
endmodule

bind imuldiv_IntMulVariable imuldiv_IntMulVariable_sva dut_sva_top (.*);

//////////////////////////////
// Control FSM + control SVA
//////////////////////////////
module imuldiv_IntMulVariableCtrl_sva
(
  input        clk,
  input        reset,
  input        mulreq_val,
  output       mulreq_rdy,
  output       mulresp_val,
  input        mulresp_rdy,
  input  [31:0] b_data,
  input         sign,
  output        sign_en,
  output        result_en,
  output        a_mux_sel,
  output        b_mux_sel,
  output [4:0] op_shamt,
  output        result_mux_sel,
  output        add_mux_sel,
  output        sign_mux_sel,
  input  [1:0]  state_reg,
  input  [1:0]  state_next
);
  // Local copies of FSM encodings
  localparam STATE_IDLE = 2'd0;
  localparam STATE_CALC = 2'd1;
  localparam STATE_SIGN = 2'd2;

  // synthesis translate_off
  default clocking @(posedge clk); endclocking
  default disable iff (reset);

  // Handshake go signals (recompute locally)
  wire mulreq_go  = mulreq_val && mulreq_rdy;
  wire mulresp_go = mulresp_val && mulresp_rdy;

  // Ready/valid are only asserted in the intended states
  assert property ((state_reg==STATE_IDLE) <-> mulreq_rdy);
  assert property ((state_reg==STATE_SIGN) <-> mulresp_val);

  // Decode correctness in states
  // IDLE: sign_en=1, result_en=1, muxes load (0)
  assert property (state_reg==STATE_IDLE |-> (sign_en && result_en && !a_mux_sel && !b_mux_sel && !result_mux_sel));
  // CALC: sign_en=0, result_en=1, muxes next (1)
  assert property (state_reg==STATE_CALC |-> (!sign_en && result_en && a_mux_sel && b_mux_sel && result_mux_sel));
  // SIGN: sign_en=0, result_en=0
  assert property (state_reg==STATE_SIGN |-> (!sign_en && !result_en));

  // FSM transitions
  assert property (state_reg==STATE_IDLE && mulreq_go  |=> state_reg==STATE_CALC);
  assert property (state_reg==STATE_CALC && ((b_data>>1)==32'b0) |=> state_reg==STATE_SIGN);
  assert property (state_reg==STATE_CALC && ((b_data>>1)!=32'b0) |=> state_reg==STATE_CALC);
  assert property (state_reg==STATE_SIGN && mulresp_go |=> state_reg==STATE_IDLE);
  // Stay in IDLE if request not accepted
  assert property (state_reg==STATE_IDLE && mulreq_val && !mulreq_rdy |=> state_reg==STATE_IDLE);

  // Control signal integrity (no X) when used
  assert property ((state_reg inside {STATE_IDLE,STATE_CALC}) |-> !$isunknown({a_mux_sel,b_mux_sel,result_mux_sel,sign_en,result_en,op_shamt}));

  // Add/sign select wiring
  assert property (add_mux_sel == b_data[0]);
  assert property (sign_mux_sel == sign);

  // op_shamt properties:
  // In CALC, it must be between 1 and 31 (never 0)
  assert property (state_reg==STATE_CALC |-> (op_shamt >= 5'd1 && op_shamt <= 5'd31));
  // If (b_data>>1)==0, encoder outputs 0 => op_shamt must be 1
  assert property (((b_data>>1)==32'b0) |-> op_shamt==5'd1);

  // Cover: full transaction path
  cover property (state_reg==STATE_IDLE && mulreq_go ##[1:40] state_reg==STATE_SIGN && mulresp_val ##1 mulresp_go);

  // Cover: CALC cycles with both add paths chosen
  cover property (state_reg==STATE_CALC && add_mux_sel==1);
  cover property (state_reg==STATE_CALC && add_mux_sel==0);

  // Cover: small and large shifts
  cover property (state_reg==STATE_CALC && op_shamt==5'd1);
  cover property (state_reg==STATE_CALC && op_shamt==5'd31);
  // synthesis translate_on
endmodule

bind imuldiv_IntMulVariableCtrl imuldiv_IntMulVariableCtrl_sva ctrl_sva (.*);

/////////////////////////
// Datapath-focused SVA
/////////////////////////
module imuldiv_IntMulVariableDpath_sva
(
  input         clk,
  input         reset,
  input  [31:0] mulreq_msg_a,
  input  [31:0] mulreq_msg_b,
  input         sign_en,
  input         result_en,
  input         result_mux_sel,
  input         add_mux_sel,
  input  [4:0]  op_shamt,
  output        sign,
  input  [63:0] a_reg,
  input  [63:0] result_reg
);
  localparam op_load = 1'b0;
  localparam op_next = 1'b1;
  localparam add_old = 1'b0;
  localparam add_next= 1'b1;

  // synthesis translate_off
  default clocking @(posedge clk); endclocking
  default disable iff (reset);

  // Sign register update behavior
  assert property (sign_en |=> sign == $past(mulreq_msg_a[31]^mulreq_msg_b[31]));
  assert property (!sign_en |=> sign == $past(sign));

  // Result register update behavior
  // Load zeros when requested
  assert property (result_en && (result_mux_sel==op_load) |=> result_reg==64'b0);
  // Hold when add_old selected
  assert property (result_en && (result_mux_sel==op_next) && (add_mux_sel==add_old) |=> result_reg == $past(result_reg));
  // Accumulate when add_next selected
  assert property (result_en && (result_mux_sel==op_next) && (add_mux_sel==add_next) |=> result_reg == $past(result_reg + a_reg));

  // When not enabled, result must hold
  assert property (!result_en |=> result_reg == $past(result_reg));

  // Shift amount not zero when used (conservative)
  assert property (result_en && (result_mux_sel==op_next) |-> op_shamt!=5'd0);
  // synthesis translate_on
endmodule

bind imuldiv_IntMulVariableDpath imuldiv_IntMulVariableDpath_sva dpath_sva (.*);

//////////////////////////////////////
// Encoder functional correctness SVA
//////////////////////////////////////
module vc_32_5_ReversePriorityEncoder_sva
(
  input  [31:0] in_bits,
  output        out_val,
  output  [4:0] out_bits
);
  // synthesis translate_off
  // Combinational assertions (no clock needed)
  // out_val matches non-zero detection
  assert final (out_val == (in_bits != 32'b0));

  // For one-hot inputs, out_bits must point to the set bit
  assert final ($onehot(in_bits) -> (in_bits == (32'h1 << out_bits)));

  // Quick sanity on lowest bit
  assert final (in_bits[0] -> (out_bits==5'd0));
  // synthesis translate_on
endmodule

bind vc_32_5_ReversePriorityEncoder vc_32_5_ReversePriorityEncoder_sva enc_sva (.*);