// SVA for wb_bridge_16_32
// Bind into DUT to check key behavior concisely

module wb_bridge_16_32_sva #(parameter AWIDTH=16) (
  input logic                   wb_clk,
  input logic                   wb_rst,
  // A-side
  input logic                   A_cyc_i,
  input logic                   A_stb_i,
  input logic                   A_we_i,
  input logic [3:0]             A_sel_i,
  input logic [AWIDTH-1:0]      A_adr_i,
  input logic [31:0]            A_dat_i,
  output logic [31:0]           A_dat_o,
  output logic                  A_ack_o,
  // B-side
  output logic                  B_cyc_o,
  output logic                  B_stb_o,
  output logic                  B_we_o,
  output logic [1:0]            B_sel_o,
  output logic [AWIDTH-1:0]     B_adr_o,
  output logic [15:0]           B_dat_o,
  input  logic [15:0]           B_dat_i,
  input  logic                  B_ack_i,
  // DUT internals (bind these to DUT regs)
  input logic                   phase,
  input logic [15:0]            holding
);

  default clocking cb @(posedge wb_clk); endclocking
  default disable iff (wb_rst);

  // Reset behavior
  assert property (wb_rst |=> phase == 1'b0);

  // Phase toggles only on B_ack_i and is otherwise stable
  assert property (B_ack_i |=> phase != $past(phase));
  assert property (!B_ack_i |=> phase == $past(phase));

  // Acknowledge mapping
  assert property (A_ack_o === (phase & B_ack_i));
  assert property ((B_ack_i && !phase) |-> !A_ack_o);

  // Pass-through controls
  assert property (B_cyc_o == A_cyc_i);
  assert property (B_stb_o == A_stb_i);
  assert property (B_we_o  == A_we_i);

  // Address mapping: {A[AW-1:2], phase, 1'b0}
  assert property (B_adr_o == {A_adr_i[AWIDTH-1:2], phase, 1'b0});

  // Halfword data/select steering
  assert property ((!phase) |-> (B_dat_o == A_dat_i[15:0]  && B_sel_o == A_sel_i[1:0]));
  assert property (( phase) |-> (B_dat_o == A_dat_i[31:16] && B_sel_o == A_sel_i[3:2]));

  // Holding register captures lower halfword on low-phase ack
  assert property ((B_ack_i && !phase) |=> holding == $past(B_dat_i));

  // Read data reconstruction delivered on high-phase ack
  // Upper = current B_dat_i, lower = data captured at last low-phase ack
  assert property ((B_ack_i && phase)
                   |-> A_ack_o && (A_dat_o == {B_dat_i, $past(B_dat_i, 0, (B_ack_i && !phase))}));

  // Basic cover: one complete two-beat transaction (low-ack then high-ack)
  cover property ((B_ack_i && !phase) ##[1:16] (B_ack_i && phase) ##0 A_ack_o);

  // Cover both read and write two-beat sequences
  cover property (A_we_i==1 && (B_ack_i && !phase) ##[1:16] (B_ack_i && phase) ##0 A_ack_o);
  cover property (A_we_i==0 && (B_ack_i && !phase) ##[1:16] (B_ack_i && phase) ##0 A_ack_o);

endmodule

// Bind into all instances of the DUT; connects internals 'phase' and 'holding'
bind wb_bridge_16_32 wb_bridge_16_32_sva #(.AWIDTH(AWIDTH)) wb_bridge_16_32_sva_i (
  .wb_clk, .wb_rst,
  .A_cyc_i, .A_stb_i, .A_we_i, .A_sel_i, .A_adr_i, .A_dat_i, .A_dat_o, .A_ack_o,
  .B_cyc_o, .B_stb_o, .B_we_o, .B_sel_o, .B_adr_o, .B_dat_o, .B_dat_i, .B_ack_i,
  .phase(phase), .holding(holding)
);