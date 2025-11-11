// SVA checker for axi_dwidth_converter_v2_1_8_w_downsizer
// Bind this checker to the DUT instance. Focused, high-quality protocol and functional checks.

module axi_dwidth_converter_v2_1_8_w_downsizer_sva #(
  parameter string  C_FAMILY               = "none",
  parameter int     C_S_AXI_DATA_WIDTH     = 64,
  parameter int     C_M_AXI_DATA_WIDTH     = 32,
  parameter int     C_S_AXI_BYTES_LOG      = 3,
  parameter int     C_M_AXI_BYTES_LOG      = 2,
  parameter int     C_RATIO_LOG            = 1
)(
  // DUT ports
  input  logic                            ARESET,
  input  logic                            ACLK,

  input  logic                            cmd_valid,
  input  logic                            cmd_mirror,
  input  logic                            cmd_fix,
  input  logic [C_S_AXI_BYTES_LOG-1:0]    cmd_first_word, 
  input  logic [C_S_AXI_BYTES_LOG-1:0]    cmd_offset,
  input  logic [C_S_AXI_BYTES_LOG-1:0]    cmd_mask,
  input  logic [C_M_AXI_BYTES_LOG:0]      cmd_step,
  input  logic [3-1:0]                    cmd_size,
  input  logic [8-1:0]                    cmd_length,
  output logic                            cmd_ready,
   
  input  logic [C_S_AXI_DATA_WIDTH-1:0]   S_AXI_WDATA,
  input  logic [C_S_AXI_DATA_WIDTH/8-1:0] S_AXI_WSTRB,
  input  logic                            S_AXI_WLAST,
  input  logic                            S_AXI_WVALID,
  output logic                            S_AXI_WREADY,

  output logic [C_M_AXI_DATA_WIDTH-1:0]   M_AXI_WDATA,
  output logic [C_M_AXI_DATA_WIDTH/8-1:0] M_AXI_WSTRB,
  output logic                            M_AXI_WLAST,
  output logic                            M_AXI_WVALID,
  input  logic                            M_AXI_WREADY,

  // DUT internals (connected via bind by name)
  input  logic                            word_completed,
  input  logic [C_RATIO_LOG-1:0]          current_index,
  input  logic                            last_beat,
  input  logic                            last_word,
  input  logic [C_S_AXI_BYTES_LOG-1:0]    size_mask,
  input  logic [C_S_AXI_BYTES_LOG-1:0]    next_word,
  input  logic                            first_word,
  input  logic                            first_mi_word,
  input  logic [7:0]                      length_counter,
  input  logic [7:0]                      next_length_counter,
  input  logic [C_S_AXI_BYTES_LOG-1:0]    current_word_1,
  input  logic [7:0]                      length_counter_1,
  input  logic                            pop_mi_data,
  input  logic                            mi_stalling
);

  localparam int DW_S = C_S_AXI_DATA_WIDTH;
  localparam int DW_M = C_M_AXI_DATA_WIDTH;
  localparam int SW_S = DW_S/8;
  localparam int SW_M = DW_M/8;
  localparam int RATIO = (DW_S/DW_M);

  default clocking cb @(posedge ACLK); endclocking
  default disable iff (ARESET);

  // Structural equivalences
  assert property (M_AXI_WVALID == (S_AXI_WVALID & cmd_valid));
  assert property (S_AXI_WREADY == (cmd_valid & word_completed & M_AXI_WREADY));
  assert property (cmd_ready     == (cmd_valid & M_AXI_WVALID & M_AXI_WREADY & last_word));
  assert property (M_AXI_WLAST   == last_word);
  assert property (mi_stalling   == (M_AXI_WVALID & ~M_AXI_WREADY));
  assert property (last_beat     == (length_counter == 8'h00));
  assert property (last_word     == last_beat);

  // AXI stability while stalled
  assert property (S_AXI_WVALID & ~S_AXI_WREADY |-> S_AXI_WVALID throughout (!S_AXI_WREADY))
    else $error("S_AXI_WVALID dropped while not ready");
  assert property (S_AXI_WVALID & ~S_AXI_WREADY |-> $stable(S_AXI_WDATA) and $stable(S_AXI_WSTRB) and $stable(S_AXI_WLAST) until S_AXI_WREADY);

  assert property (M_AXI_WVALID & ~M_AXI_WREADY |-> M_AXI_WVALID throughout (!M_AXI_WREADY))
    else $error("M_AXI_WVALID dropped while not ready");
  assert property (M_AXI_WVALID & ~M_AXI_WREADY |-> $stable(M_AXI_WDATA) and $stable(M_AXI_WSTRB) and $stable(M_AXI_WLAST) until M_AXI_WREADY);

  // Ready implications
  assert property (S_AXI_WREADY |-> (cmd_valid & M_AXI_WREADY));

  // Data/STRB downsizing mapping on each MI handshake
  assert property ((M_AXI_WVALID & M_AXI_WREADY) |-> 
                   (M_AXI_WDATA == S_AXI_WDATA[current_index*DW_M +: DW_M] &&
                    M_AXI_WSTRB == S_AXI_WSTRB[current_index*SW_M +: SW_M]));

  // State/register update checks on pop
  assert property (pop_mi_data |=> current_word_1 == $past(next_word));
  assert property (pop_mi_data |=> length_counter_1 == $past(next_length_counter));

  // first_word/first_mi_word control around WLAST
  assert property (pop_mi_data &&  M_AXI_WLAST |=>  first_word);
  assert property (pop_mi_data && !M_AXI_WLAST |=> !first_word);
  assert property (pop_mi_data &&  M_AXI_WLAST |=>  first_mi_word);
  assert property (pop_mi_data && !M_AXI_WLAST |=> !first_mi_word);

  // Reset effects (checked in-cycle of reset assertion)
  assert property (@(posedge ACLK) ARESET |-> (first_word && first_mi_word));

  // Sanity: size_mask not X when used
  assert property (cmd_valid |-> !$isunknown(size_mask));

  // Coverage: stalls, multi-beat, last, cmd modes, lane usage
  cover property (S_AXI_WVALID && !S_AXI_WREADY [*2] ##1 S_AXI_WVALID && S_AXI_WREADY);
  cover property (M_AXI_WVALID && !M_AXI_WREADY [*2] ##1 M_AXI_WVALID && M_AXI_WREADY);
  cover property ((M_AXI_WVALID && M_AXI_WREADY) ##1 (!M_AXI_WLAST && M_AXI_WVALID && M_AXI_WREADY) ##1 (M_AXI_WVALID && M_AXI_WREADY && M_AXI_WLAST));
  cover property (cmd_valid && cmd_fix     && word_completed && S_AXI_WREADY);
  cover property (cmd_valid && cmd_mirror  && word_completed && S_AXI_WREADY);
  cover property (cmd_valid && !cmd_fix && !cmd_mirror && word_completed && S_AXI_WREADY);
  if (C_RATIO_LOG > 0) begin
    cover property (M_AXI_WVALID && M_AXI_WREADY && (current_index == '0));
    cover property (M_AXI_WVALID && M_AXI_WREADY && (current_index == (RATIO-1)));
  end

endmodule

// Bind into DUT (connects by name to ports and internals)
bind axi_dwidth_converter_v2_1_8_w_downsizer
  axi_dwidth_converter_v2_1_8_w_downsizer_sva #(
    .C_FAMILY(C_FAMILY),
    .C_S_AXI_DATA_WIDTH(C_S_AXI_DATA_WIDTH),
    .C_M_AXI_DATA_WIDTH(C_M_AXI_DATA_WIDTH),
    .C_S_AXI_BYTES_LOG(C_S_AXI_BYTES_LOG),
    .C_M_AXI_BYTES_LOG(C_M_AXI_BYTES_LOG),
    .C_RATIO_LOG(C_RATIO_LOG)
  ) i_axi_dwidth_converter_v2_1_8_w_downsizer_sva (.*);