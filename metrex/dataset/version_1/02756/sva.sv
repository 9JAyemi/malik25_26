// SVA for qmem_decoder
// Quality-focused, concise checks and coverage

module qmem_decoder_assert #(
  parameter QAW = 32,
  parameter QDW = 32,
  parameter QSW = QDW/8,
  parameter SN  = 2
)(
  input  wire              clk,
  input  wire              rst,
  input  wire              qm_cs,
  input  wire              qm_we,
  input  wire    [QAW-1:0] qm_adr,
  input  wire    [QSW-1:0] qm_sel,
  input  wire    [QDW-1:0] qm_dat_w,
  output wire    [QDW-1:0] qm_dat_r,
  output wire              qm_ack,
  output wire              qm_err,
  output wire [SN    -1:0] qs_cs,
  output wire [SN    -1:0] qs_we,
  output wire [SN*QAW-1:0] qs_adr,
  output wire [SN*QSW-1:0] qs_sel,
  output wire [SN*QDW-1:0] qs_dat_w,
  input  wire [SN*QDW-1:0] qs_dat_r,
  input  wire [SN    -1:0] qs_ack,
  input  wire [SN    -1:0] qs_err,
  input  wire [SN    -1:0] ss,
  input  wire        [7:0] ss_a,
  input  wire        [7:0] ss_r
);

  default clocking cb @(posedge clk); endclocking
  // Disable assertions under reset
  `define DISABLE_RST disable iff (rst)

  // Helper: pick data slice
  function automatic [QDW-1:0] pick_qs_dat(input [SN*QDW-1:0] bus, input int unsigned idx);
    pick_qs_dat = bus >> (QDW*idx);
  endfunction

  // 1) Basic structural/connectivity checks
  genvar i;
  generate for (i=0; i<SN; i++) begin: GEN_CONN_ASSERTS
    // cs gating by ss
    assert property (`DISABLE_RST 1'b1 |-> (qs_cs[i] == (qm_cs & ss[i])));
    // we broadcast
    assert property (`DISABLE_RST 1'b1 |-> (qs_we[i] == qm_we));
    // address/select/data broadcast
    assert property (`DISABLE_RST 1'b1 |-> (qs_adr[QAW*(i+1)-1 -: QAW] == qm_adr));
    assert property (`DISABLE_RST 1'b1 |-> (qs_sel[QSW*(i+1)-1 -: QSW] == qm_sel));
    assert property (`DISABLE_RST 1'b1 |-> (qs_dat_w[QDW*(i+1)-1 -: QDW] == qm_dat_w));
    // slave must not assert ack/err unless selected and master active
    assert property (`DISABLE_RST qs_ack[i] |-> (qm_cs && ss[i]));
    assert property (`DISABLE_RST qs_err[i] |-> (qm_cs && ss[i]));
    // per-slave ack/err mutually exclusive
    assert property (`DISABLE_RST !(qs_ack[i] && qs_err[i]));
  end endgenerate

  // 2) Selection vector well-formed, stable during a transaction
  assert property (`DISABLE_RST qm_cs |-> $onehot0(ss));
  assert property (`DISABLE_RST (qm_cs && !qm_ack && !qm_err) |-> $stable(ss) until_with (qm_ack || qm_err));

  // 3) No response if no slave selected
  assert property (`DISABLE_RST (qm_cs && (ss == '0)) |-> (!qm_ack && !qm_err));

  // 4) Global ack/err mapping and exclusivity
  assert property (`DISABLE_RST !(qm_ack && qm_err));
  // mapping matches implementation (selected bit via shift)
  assert property (`DISABLE_RST qm_ack == ( (qs_ack >> ss_a)[0] ));
  assert property (`DISABLE_RST qm_err == ( (qs_err >> ss_a)[0] ));
  // If ss is one-hot, qm_* equals that selected slave's response
  assert property (`DISABLE_RST (qm_cs && $onehot(ss)) |-> (qm_ack == ((qs_ack & ss) != '0)));
  assert property (`DISABLE_RST (qm_cs && $onehot(ss)) |-> (qm_err == ((qs_err & ss) != '0)));

  // 5) Return data selection/latched index behavior
  // ss_r updates to ss_a on read response; stable on write response
  assert property (`DISABLE_RST (qm_cs && !qm_we && (qm_ack || qm_err)) |=> (ss_r == $past(ss_a)));
  assert property (`DISABLE_RST (qm_cs &&  qm_we && (qm_ack || qm_err)) |=> $stable(ss_r));
  // After a read response, qm_dat_r matches the returned slave's data (next cycle)
  assert property (`DISABLE_RST (qm_cs && !qm_we && (qm_ack || qm_err)) |=> (qm_dat_r == pick_qs_dat(qs_dat_r, $past(ss_a))));

  // 6) No unselected slave may respond while a request is active
  assert property (`DISABLE_RST qm_cs |-> ((qs_ack & ~ss) == '0));
  assert property (`DISABLE_RST qm_cs |-> ((qs_err & ~ss) == '0));

  // 7) Coverage
  generate for (i=0; i<SN; i++) begin: GEN_COV
    cover property (`DISABLE_RST qm_cs && ss[i] && !qm_we ##1 qs_ack[i]);
    cover property (`DISABLE_RST qm_cs && ss[i] &&  qm_we ##1 qs_ack[i]);
    cover property (`DISABLE_RST qm_cs && ss[i]           ##1 qs_err[i]);
  end endgenerate
  cover property (`DISABLE_RST qm_cs && (ss == '0));
  cover property (`DISABLE_RST qm_cs && $onehot(ss));

endmodule

// Bind into DUT
bind qmem_decoder qmem_decoder_assert #(.QAW(QAW), .QDW(QDW), .QSW(QSW), .SN(SN)) qmem_decoder_assert_i (.*);