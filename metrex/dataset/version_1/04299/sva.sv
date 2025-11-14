// SVA for axi_data_fifo_v2_1_7_ndeep_srl
module axi_data_fifo_v2_1_7_ndeep_srl_sva #(
  parameter string C_FAMILY = "rtl",
  parameter int unsigned C_A_WIDTH = 1
)(
  input  logic                       CLK,
  input  logic [C_A_WIDTH-1:0]       A,
  input  logic                       CE,
  input  logic                       D,
  input  logic                       Q
);

  // Effective depth is 32 for <=5-bit address, else 2**C_A_WIDTH
  localparam int unsigned DEPTH = (C_A_WIDTH <= 5) ? 32 : (1 << C_A_WIDTH);
  localparam int unsigned IDXW  = (C_A_WIDTH <= 5) ? 5  : C_A_WIDTH;

  // Address used by DUT (A zero-extended to 5 when C_A_WIDTH<=5)
  logic [IDXW-1:0] idx;
  always_comb begin
    idx = (C_A_WIDTH <= 5) ? {{(5-C_A_WIDTH){1'b0}}, A} : A;
  end

  // Simple golden model of the shifter (updates only when CE=1)
  logic [DEPTH-1:0] shadow;
  initial shadow = '0;
  always_ff @(posedge CLK) begin
    if (CE) shadow <= {shadow[DEPTH-2:0], D};
  end

  default clocking cb @(posedge CLK); endclocking

  // Core functional check: Q matches the modeled tap
  ap_q_matches_model: assert property (Q == shadow[idx]);

  // When no write and address is stable, Q must hold
  ap_hold_when_no_we_addr_stable: assert property (!CE && $stable(idx) |-> $stable(Q));

  // Lightweight timing sanity: tap 0 and tap 1 under consecutive enables
  ap_tap0_one_step: assert property ($past(CE) && (idx == 0) |-> Q == $past(D));
  ap_tap1_two_steps: assert property ($past(CE,1) && $past(CE,2) && (idx == 1) |-> Q == $past(D,2));

  // Coverage
  cp_ce:       cover property (CE);
  cp_burst:    cover property (CE[*3]);
  cp_idx0:     cover property (CE && (idx == 0));
  cp_idxmax:   cover property (CE && (idx == DEPTH-1));
  cp_qchange:  cover property ($changed(Q));
  cp_data_to_tap0: cover property (CE && D ##1 (idx == 0 && Q));

endmodule

bind axi_data_fifo_v2_1_7_ndeep_srl
  axi_data_fifo_v2_1_7_ndeep_srl_sva #(
    .C_FAMILY(C_FAMILY),
    .C_A_WIDTH(C_A_WIDTH)
  ) sva_i (
    .CLK(CLK),
    .A(A),
    .CE(CE),
    .D(D),
    .Q(Q)
  );