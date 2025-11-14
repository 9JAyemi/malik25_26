// SVA for dc_rep_upload
// Bind into DUT to check key protocol, state/counter behavior, ctrl encoding,
// data mapping, reset, and configuration behavior.

bind dc_rep_upload dc_rep_upload_sva sva_i (
  .clk(clk), .rst(rst),
  .dc_flits_rep(dc_flits_rep),
  .v_dc_flits_rep(v_dc_flits_rep),
  .flits_max(flits_max),
  .en_flits_max(en_flits_max),
  .rep_fifo_rdy(rep_fifo_rdy),
  .dc_flit_out(dc_flit_out),
  .v_dc_flit_out(v_dc_flit_out),
  .dc_ctrl_out(dc_ctrl_out),
  .dc_rep_upload_state(dc_rep_upload_state),

  // internal
  .dc_rep_state(dc_rep_state),
  .dc_rep_flits(dc_rep_flits),
  .sel_cnt(sel_cnt),
  .fsm_rst(fsm_rst),
  .next(next),
  .en_flits_in(en_flits_in),
  .inc_cnt(inc_cnt),
  .flits_max_reg(flits_max_reg)
);

module dc_rep_upload_sva
(
  input  logic                 clk,
  input  logic                 rst,
  input  logic [175:0]         dc_flits_rep,
  input  logic                 v_dc_flits_rep,
  input  logic [3:0]           flits_max,
  input  logic                 en_flits_max,
  input  logic                 rep_fifo_rdy,
  input  logic [15:0]          dc_flit_out,
  input  logic                 v_dc_flit_out,
  input  logic [1:0]           dc_ctrl_out,
  input  logic                 dc_rep_upload_state,

  // internal
  input  logic                 dc_rep_state,
  input  logic [175:0]         dc_rep_flits,
  input  logic [3:0]           sel_cnt,
  input  logic                 fsm_rst,
  input  logic                 next,
  input  logic                 en_flits_in,
  input  logic                 inc_cnt,
  input  logic [3:0]           flits_max_reg
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Shorthands
  let busy     = dc_rep_upload_state;
  let g_valid  = busy && rep_fifo_rdy;

  // Output port mirrors internal state
  assert property (dc_rep_upload_state == dc_rep_state);

  // Reset effects next cycle
  assert property (rst |=> (!dc_rep_upload_state && sel_cnt==0 && flits_max_reg==0 && dc_rep_flits==176'h0));

  // Start-of-transfer handshake (idle + v_dc_flits_rep -> busy next, data captured)
  assert property (!busy && v_dc_flits_rep |=> busy);
  assert property (!busy && v_dc_flits_rep |=> dc_rep_flits == $past(dc_flits_rep));

  // While busy (until fsm_rst), payload buffer is stable
  assert property (disable iff (rst || fsm_rst) busy |-> $stable(dc_rep_flits));

  // Legal configuration: only 11 flits (0..10) are implemented by mux
  assert property (flits_max_reg <= 4'd10);

  // flits_max register capture and reset
  assert property (en_flits_max |=> flits_max_reg == $past(flits_max));
  assert property (fsm_rst |=> flits_max_reg == 0);

  // v_dc_flit_out strictly when busy && rep_fifo_rdy
  assert property (g_valid |-> v_dc_flit_out);
  assert property (v_dc_flit_out |-> g_valid);

  // ctrl_out encoding
  assert property (g_valid && (sel_cnt==flits_max_reg)         |-> (dc_ctrl_out==2'b11));
  assert property (g_valid && (sel_cnt==4'd0) && (sel_cnt!=flits_max_reg) |-> (dc_ctrl_out==2'b01));
  assert property (g_valid && (sel_cnt!=4'd0) && (sel_cnt!=flits_max_reg) |-> (dc_ctrl_out==2'b10));
  assert property (!g_valid |-> dc_ctrl_out==2'b00);

  // Counter behavior
  assert property (g_valid && sel_cnt!=flits_max_reg |=> sel_cnt == $past(sel_cnt)+1);
  assert property (g_valid && sel_cnt==flits_max_reg |=> sel_cnt == 0);
  assert property (busy && !rep_fifo_rdy |=> $stable(sel_cnt));

  // End-of-packet effects next cycle
  assert property (g_valid && sel_cnt==flits_max_reg |=> (!busy && sel_cnt==0 && dc_rep_flits==176'h0));

  // Data mapping for each valid flit
  assert property (v_dc_flit_out |->
      ((sel_cnt==4'd0  && dc_flit_out==dc_rep_flits[175:160]) ||
       (sel_cnt==4'd1  && dc_flit_out==dc_rep_flits[159:144]) ||
       (sel_cnt==4'd2  && dc_flit_out==dc_rep_flits[143:128]) ||
       (sel_cnt==4'd3  && dc_flit_out==dc_rep_flits[127:112]) ||
       (sel_cnt==4'd4  && dc_flit_out==dc_rep_flits[111:96])  ||
       (sel_cnt==4'd5  && dc_flit_out==dc_rep_flits[95:80])   ||
       (sel_cnt==4'd6  && dc_flit_out==dc_rep_flits[79:64])   ||
       (sel_cnt==4'd7  && dc_flit_out==dc_rep_flits[63:48])   ||
       (sel_cnt==4'd8  && dc_flit_out==dc_rep_flits[47:32])   ||
       (sel_cnt==4'd9  && dc_flit_out==dc_rep_flits[31:16])   ||
       (sel_cnt==4'd10 && dc_flit_out==dc_rep_flits[15:0]))
  );

  // Combinational control intent checks from FSM decode
  assert property (!busy |-> (en_flits_in == v_dc_flits_rep && next == v_dc_flits_rep && inc_cnt==0));
  assert property (busy  |-> (en_flits_in == 1'b0 && next == 1'b0 && inc_cnt==rep_fifo_rdy));

  // Coverage
  cover property (!busy && v_dc_flits_rep ##1 busy ##[1:$] (g_valid && sel_cnt==0 && dc_ctrl_out==2'b01));
  cover property (g_valid && dc_ctrl_out==2'b10);
  cover property (g_valid && dc_ctrl_out==2'b11);
  cover property (en_flits_max && flits_max==4'd0);
  cover property (en_flits_max && flits_max==4'd1);
  cover property (en_flits_max && flits_max==4'd10);
  cover property (busy && !rep_fifo_rdy ##1 !rep_fifo_rdy ##1 g_valid);

endmodule