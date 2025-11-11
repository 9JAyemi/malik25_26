// SVA for acc_vadd_hls
// Bind this module to the DUT instance(s)

module acc_vadd_hls_sva (
  input  logic        ap_clk,
  input  logic        ap_rst_n,

  input  logic [31:0] cmd_TDATA,
  input  logic        cmd_TVALID,
  input  logic        cmd_TREADY,

  input  logic [31:0] a_Dout_A,
  input  logic [31:0] b_Dout_A,

  input  logic [31:0] a_Addr_A,
  input  logic        a_EN_A,
  input  logic [3:0]  a_WEN_A,
  input  logic        a_Clk_A,
  input  logic        a_Rst_A,

  input  logic [31:0] b_Addr_A,
  input  logic        b_EN_A,
  input  logic [3:0]  b_WEN_A,
  input  logic        b_Clk_A,
  input  logic        b_Rst_A,

  input  logic [31:0] result_Addr_A,
  input  logic        result_EN_A,
  input  logic [3:0]  result_WEN_A,
  input  logic [31:0] result_Din_A,
  input  logic        result_Clk_A,
  input  logic        result_Rst_A,

  input  logic [2:0]  ap_CS_fsm,
  input  logic        resp_TVALID,
  input  logic        resp_TREADY,

  // internal regs/wires
  input  logic        tmp_reg_157,
  input  logic [31:0] end_reg_161,
  input  logic [31:0] i_reg_100,
  input  logic        tmp_2_fu_122_p2,
  input  logic        tmp_6_reg_195,
  input  logic        ap_reg_ioackin_resp_TREADY,
  input  logic        ap_sig_ioackin_resp_TREADY
);

  localparam logic [2:0] ST1=3'b000, ST2=3'b001, ST3=3'b010, ST4=3'b011, ST5=3'b100;

  default clocking cb @(posedge ap_clk); endclocking
  default disable iff (!ap_rst_n)

  // Legal state
  assert property (ap_CS_fsm inside {ST1,ST2,ST3,ST4,ST5});

  // FSM next-state checks
  assert property (ap_CS_fsm==ST1 &&  cmd_TVALID |=> ap_CS_fsm==ST2);
  assert property (ap_CS_fsm==ST1 && !cmd_TVALID |=> ap_CS_fsm==ST1);

  assert property (ap_CS_fsm==ST2 &&  cmd_TVALID |=> ap_CS_fsm==ST3);
  assert property (ap_CS_fsm==ST2 && !cmd_TVALID |=> ap_CS_fsm==ST2);

  assert property (ap_CS_fsm==ST3 &&  cmd_TVALID |=> ap_CS_fsm==ST4);
  assert property (ap_CS_fsm==ST3 && !cmd_TVALID |=> ap_CS_fsm==ST3);

  assert property (ap_CS_fsm==ST4 && ( tmp_reg_157==1'b0 || tmp_2_fu_122_p2==1'b0) |=> ap_CS_fsm==ST1);
  assert property (ap_CS_fsm==ST4 && (~tmp_reg_157==1'b0 && tmp_2_fu_122_p2==1'b1) |=> ap_CS_fsm==ST5);

  assert property (ap_CS_fsm==ST5 && !(tmp_6_reg_195 && !ap_sig_ioackin_resp_TREADY) |=> ap_CS_fsm==ST4);
  assert property (ap_CS_fsm==ST5 &&  (tmp_6_reg_195 && !ap_sig_ioackin_resp_TREADY) |=> ap_CS_fsm==ST5);

  // Command channel handshake
  assert property (cmd_TREADY |-> (cmd_TVALID && (ap_CS_fsm inside {ST1,ST2,ST3})));
  assert property ((ap_CS_fsm inside {ST1,ST2,ST3}) && cmd_TVALID |-> cmd_TREADY);

  // Command field latching
  assert property (ap_CS_fsm==ST1 && cmd_TVALID |=> tmp_reg_157 == (cmd_TDATA==32'h0000_0001));
  assert property (ap_CS_fsm==ST2 && cmd_TVALID |=> end_reg_161 == cmd_TDATA);
  assert property (ap_CS_fsm==ST3 && cmd_TVALID && tmp_reg_157 |=> i_reg_100 == cmd_TDATA);

  // Loop index increment in ST5 (except when last && no resp ready yet)
  assert property (ap_CS_fsm==ST5 && !(tmp_6_reg_195 && !ap_sig_ioackin_resp_TREADY)
                   |=> i_reg_100 == $past(i_reg_100)+32'd1);

  // Memory port attributes
  assert property (a_WEN_A==4'b0000);
  assert property (b_WEN_A==4'b0000);
  assert property (a_EN_A == (ap_CS_fsm==ST4));
  assert property (b_EN_A == (ap_CS_fsm==ST4));

  // Memory clock/reset forwarding
  assert property (a_EN_A |-> (a_Clk_A==ap_clk && a_Rst_A==ap_rst_n));
  assert property (b_EN_A |-> (b_Clk_A==ap_clk && b_Rst_A==ap_rst_n));
  assert property (result_EN_A |-> (result_Clk_A==ap_clk && result_Rst_A==ap_rst_n));

  // Address mapping
  assert property (a_EN_A |-> a_Addr_A == ($signed(i_reg_100) <<< 2));
  assert property (b_EN_A |-> b_Addr_A == ($signed(i_reg_100) <<< 2));

  // Result write enable/addr/data
  assert property (result_EN_A == (ap_CS_fsm==ST5 && !(tmp_6_reg_195 && !ap_sig_ioackin_resp_TREADY)));
  assert property (result_EN_A |-> result_WEN_A==4'hF);
  assert property (!result_EN_A |-> result_WEN_A==4'h0);

  assert property (result_Din_A == ((b_Dout_A << 1) + a_Dout_A));

  assert property (ap_CS_fsm==ST5 && $past(ap_CS_fsm)==ST4 |-> result_Addr_A == ($signed($past(i_reg_100)) <<< 2));

  // Response channel behavior (last-beat response only)
  assert property (resp_TVALID == (ap_CS_fsm==ST5 && tmp_6_reg_195 && (ap_reg_ioackin_resp_TREADY==1'b0)));

  // Response handshake effect: drop TVALID and return to ST4
  assert property (resp_TVALID && resp_TREADY |=> !resp_TVALID && ap_CS_fsm==ST4);

  // Coverage: full successful transaction including multiple iterations and response
  cover property (
    ap_CS_fsm==ST1 && cmd_TVALID && cmd_TDATA==32'h1
    ##1 ap_CS_fsm==ST2 && cmd_TVALID
    ##1 ap_CS_fsm==ST3 && cmd_TVALID
    ##1 ap_CS_fsm==ST4
    ##1 ap_CS_fsm==ST5 && !tmp_6_reg_195
    ##1 ap_CS_fsm==ST4
    ##[1:$] (ap_CS_fsm==ST5 && tmp_6_reg_195 && resp_TVALID && resp_TREADY)
  );

  // Coverage: early exit paths
  cover property (ap_CS_fsm==ST4 && tmp_reg_157==1'b0 ##1 ap_CS_fsm==ST1);
  cover property (ap_CS_fsm==ST4 && tmp_2_fu_122_p2==1'b0 ##1 ap_CS_fsm==ST1);

endmodule

// Example bind (place in a separate file or your testbench)
// bind acc_vadd_hls acc_vadd_hls_sva sva (.*);