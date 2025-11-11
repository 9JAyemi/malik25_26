// SVA for pcie_fc_cntl
// Bindable assertion module focusing on key functionality, timing, and coverage

module pcie_fc_cntl_sva #(
  parameter int P_RX_CONSTRAINT_FC_CPLD = 32,
  parameter int P_RX_CONSTRAINT_FC_CPLH = 8,
  parameter int P_TX_CONSTRAINT_FC_CPLD = 1,
  parameter int P_TX_CONSTRAINT_FC_CPLH = 1,
  parameter int P_TX_CONSTRAINT_FC_NPD  = 1,
  parameter int P_TX_CONSTRAINT_FC_NPH  = 1,
  parameter int P_TX_CONSTRAINT_FC_PD   = 32,
  parameter int P_TX_CONSTRAINT_FC_PH   = 1
)(
  input logic                pcie_user_clk,
  input logic                pcie_user_rst_n,

  input  logic [11:0]        fc_cpld,
  input  logic [7:0]         fc_cplh,
  input  logic [11:0]        fc_npd,
  input  logic [7:0]         fc_nph,
  input  logic [11:0]        fc_pd,
  input  logic [7:0]         fc_ph,

  input  logic [2:0]         fc_sel,
  input  logic               tx_cfg_gnt,

  input  logic               tx_cpld_gnt,
  input  logic               tx_mrd_gnt,
  input  logic               tx_mwr_gnt,

  // internals
  input  logic [1:0]         cur_state,
  input  logic [2:0]         r_fc_sel,
  input  logic [1:0]         r_rd_fc_sel,
  input  logic [1:0]         r_rd_fc_sel_d1,
  input  logic [1:0]         r_rd_fc_sel_d2,

  input  logic [11:0]        r_rx_available_fc_cpld,
  input  logic [7:0]         r_rx_available_fc_cplh,
  input  logic [11:0]        r_rx_available_fc_npd,
  input  logic [7:0]         r_rx_available_fc_nph,
  input  logic [11:0]        r_rx_available_fc_pd,
  input  logic [7:0]         r_rx_available_fc_ph,

  input  logic [11:0]        r_tx_available_fc_cpld,
  input  logic [7:0]         r_tx_available_fc_cplh,
  input  logic [11:0]        r_tx_available_fc_npd,
  input  logic [7:0]         r_tx_available_fc_nph,
  input  logic [11:0]        r_tx_available_fc_pd,
  input  logic [7:0]         r_tx_available_fc_ph,

  input  logic               w_rx_available_fc_cpld,
  input  logic               w_rx_available_fc_cplh,

  input  logic               w_tx_available_fc_cpld,
  input  logic               w_tx_available_fc_cplh,
  input  logic               w_tx_available_fc_npd,
  input  logic               w_tx_available_fc_nph,
  input  logic               w_tx_available_fc_pd,
  input  logic               w_tx_available_fc_ph,

  input  logic               r_tx_cpld_gnt,
  input  logic               r_tx_mrd_gnt,
  input  logic               r_tx_mwr_gnt
);

  default clocking cb @(posedge pcie_user_clk); endclocking
  default disable iff (!pcie_user_rst_n)

  // Constants from DUT encoding
  localparam logic [1:0] S_RX_AVAILABLE_FC_SEL = 2'b01;
  localparam logic [1:0] S_TX_AVAILABLE_FC_SEL = 2'b10;

  // Basic sanity
  assert property (tx_cfg_gnt);

  // Reset behavior
  assert property (!pcie_user_rst_n |-> cur_state == S_RX_AVAILABLE_FC_SEL);
  assert property (!pcie_user_rst_n |-> r_rd_fc_sel_d1 == 2'b00 && r_rd_fc_sel_d2 == 2'b00);
  assert property (!pcie_user_rst_n |-> 
    r_rx_available_fc_cpld==0 && r_rx_available_fc_cplh==0 &&
    r_rx_available_fc_npd==0  && r_rx_available_fc_nph==0  &&
    r_rx_available_fc_pd==0   && r_rx_available_fc_ph==0   &&
    r_tx_available_fc_cpld==0 && r_tx_available_fc_cplh==0 &&
    r_tx_available_fc_npd==0  && r_tx_available_fc_nph==0  &&
    r_tx_available_fc_pd==0   && r_tx_available_fc_ph==0);

  // FSM alternates every cycle
  assert property (cur_state==S_RX_AVAILABLE_FC_SEL |-> ##1 cur_state==S_TX_AVAILABLE_FC_SEL);
  assert property (cur_state==S_TX_AVAILABLE_FC_SEL |-> ##1 cur_state==S_RX_AVAILABLE_FC_SEL);

  // Selections match state
  assert property (cur_state==S_RX_AVAILABLE_FC_SEL |-> r_fc_sel==3'b000 && r_rd_fc_sel==2'b01 && fc_sel==3'b000);
  assert property (cur_state==S_TX_AVAILABLE_FC_SEL |-> r_fc_sel==3'b100 && r_rd_fc_sel==2'b10 && fc_sel==3'b100);
  assert property (fc_sel inside {3'b000,3'b100});

  // Pipeline delays
  assert property (r_rd_fc_sel_d1 == $past(r_rd_fc_sel));
  assert property (r_rd_fc_sel_d2 == $past(r_rd_fc_sel_d1));
  assert property ($past($rose(pcie_user_rst_n),2) |-> $onehot(r_rd_fc_sel_d2));
  assert property ($past($rose(pcie_user_rst_n),3) |-> r_rd_fc_sel_d2 == ~$past(r_rd_fc_sel_d2));

  // Sampling behavior
  assert property (r_rd_fc_sel_d2[0] |-> 
    r_rx_available_fc_cpld==fc_cpld && r_rx_available_fc_cplh==fc_cplh &&
    r_rx_available_fc_npd==fc_npd   && r_rx_available_fc_nph==fc_nph   &&
    r_rx_available_fc_pd==fc_pd     && r_rx_available_fc_ph==fc_ph);

  assert property (r_rd_fc_sel_d2[1] |-> 
    r_tx_available_fc_cpld==fc_cpld && r_tx_available_fc_cplh==fc_cplh &&
    r_tx_available_fc_npd==fc_npd   && r_tx_available_fc_nph==fc_nph   &&
    r_tx_available_fc_pd==fc_pd     && r_tx_available_fc_ph==fc_ph);

  // Comparator wires correctness
  assert property (w_rx_available_fc_cpld == (r_rx_available_fc_cpld > P_RX_CONSTRAINT_FC_CPLD));
  assert property (w_rx_available_fc_cplh == (r_rx_available_fc_cplh > P_RX_CONSTRAINT_FC_CPLH));

  assert property (w_tx_available_fc_cpld == (r_tx_available_fc_cpld > P_TX_CONSTRAINT_FC_CPLD));
  assert property (w_tx_available_fc_cplh == (r_tx_available_fc_cplh > P_TX_CONSTRAINT_FC_CPLH));
  assert property (w_tx_available_fc_npd  == (r_tx_available_fc_npd  > P_TX_CONSTRAINT_FC_NPD));
  assert property (w_tx_available_fc_nph  == (r_tx_available_fc_nph  > P_TX_CONSTRAINT_FC_NPH));
  assert property (w_tx_available_fc_pd   == (r_tx_available_fc_pd   > P_TX_CONSTRAINT_FC_PD));
  assert property (w_tx_available_fc_ph   == (r_tx_available_fc_ph   > P_TX_CONSTRAINT_FC_PH));

  // Grant timing equals previous-cycle wire conditions
  assert property (r_tx_cpld_gnt == $past(w_tx_available_fc_cpld & w_tx_available_fc_cplh));
  assert property (r_tx_mrd_gnt  == $past((w_tx_available_fc_npd & w_tx_available_fc_nph) &
                                          (w_rx_available_fc_cpld & w_rx_available_fc_cplh)));
  assert property (r_tx_mwr_gnt  == $past(w_tx_available_fc_pd & w_tx_available_fc_ph));

  // Outputs equal regs (combinational assignments)
  assert property (tx_cpld_gnt == r_tx_cpld_gnt);
  assert property (tx_mrd_gnt  == r_tx_mrd_gnt);
  assert property (tx_mwr_gnt  == r_tx_mwr_gnt);

  // No X on key outputs post-reset
  assert property (!$isunknown({fc_sel, tx_cfg_gnt, tx_cpld_gnt, tx_mrd_gnt, tx_mwr_gnt}));

  // Coverage
  cover property ($rose(pcie_user_rst_n) ##2 r_rd_fc_sel_d2==2'b01 ##1 r_rd_fc_sel_d2==2'b10 ##1 r_rd_fc_sel_d2==2'b01);
  cover property (w_tx_available_fc_cpld && w_tx_available_fc_cplh);
  cover property (w_tx_available_fc_pd   && w_tx_available_fc_ph);
  cover property ((w_tx_available_fc_npd && w_tx_available_fc_nph) && (w_rx_available_fc_cpld && w_rx_available_fc_cplh));
  cover property (r_tx_cpld_gnt);
  cover property (r_tx_mrd_gnt);
  cover property (r_tx_mwr_gnt);

endmodule

// Bind into the DUT (connects by name)
bind pcie_fc_cntl pcie_fc_cntl_sva #(
  .P_RX_CONSTRAINT_FC_CPLD(P_RX_CONSTRAINT_FC_CPLD),
  .P_RX_CONSTRAINT_FC_CPLH(P_RX_CONSTRAINT_FC_CPLH),
  .P_TX_CONSTRAINT_FC_CPLD(P_TX_CONSTRAINT_FC_CPLD),
  .P_TX_CONSTRAINT_FC_CPLH(P_TX_CONSTRAINT_FC_CPLH),
  .P_TX_CONSTRAINT_FC_NPD (P_TX_CONSTRAINT_FC_NPD),
  .P_TX_CONSTRAINT_FC_NPH (P_TX_CONSTRAINT_FC_NPH),
  .P_TX_CONSTRAINT_FC_PD  (P_TX_CONSTRAINT_FC_PD),
  .P_TX_CONSTRAINT_FC_PH  (P_TX_CONSTRAINT_FC_PH)
) u_pcie_fc_cntl_sva (.*);