// SVA checker for arbitro. Bind this file to the DUT.
module arbitro_sva (
  input  logic [2:0] pe_request_bundle,
  input  logic [2:0] north_request_bundle,
  input  logic [2:0] east_request_bundle,
  input  logic [1:0] pe_cfg_bundle,
  input  logic [2:0] south_cfg_bundle,
  input  logic [2:0] west_cfg_bundle,
  input  logic       r2pe_ack
);

  // Mirror DUT encodings
  localparam logic [2:0] MUX_EAST  = 3'b111;
  localparam logic [2:0] MUX_NORTH = 3'b101;
  localparam logic [2:0] MUX_PE    = 3'b001;
  localparam logic [2:0] MUX_NULL  = 3'b000;
  localparam logic [1:0] PE_NULL   = 2'b00;
  localparam logic [1:0] PE_NORTH  = 2'b01;
  localparam logic [1:0] PE_EAST   = 2'b11;

  // Decodes
  wire [2:0] rv    = {east_request_bundle[0], north_request_bundle[0], pe_request_bundle[0]};
  wire [1:0] pe_s  = pe_request_bundle[2:1];
  wire [1:0] n_s   = north_request_bundle[2:1];
  wire [1:0] e_s   = east_request_bundle[2:1];

  // Event-based "clock" on input changes; check outputs after ##0 (delta)
  event comb_ev;
  always @(pe_request_bundle or north_request_bundle or east_request_bundle) -> comb_ev;
  default clocking cb @ (comb_ev); endclocking
  default disable iff ($isunknown({pe_request_bundle,north_request_bundle,east_request_bundle}));

  // Sanity encodings and X-checks
  assert property (1 |-> ##0 (west_cfg_bundle  inside {MUX_NULL,MUX_PE,MUX_NORTH,MUX_EAST}));
  assert property (1 |-> ##0 (south_cfg_bundle inside {MUX_NULL,MUX_PE,MUX_NORTH,MUX_EAST}));
  assert property (1 |-> ##0 (pe_cfg_bundle    inside {PE_NULL,PE_NORTH,PE_EAST}));
  assert property (!$isunknown({pe_request_bundle,north_request_bundle,east_request_bundle}) |-> ##0
                   !$isunknown({pe_cfg_bundle,south_cfg_bundle,west_cfg_bundle,r2pe_ack}));

  // rv == 000
  assert property ((rv==3'b000) |-> ##0 (west_cfg_bundle==MUX_NULL && south_cfg_bundle==MUX_NULL &&
                                         pe_cfg_bundle==PE_NULL && !r2pe_ack));

  // rv == 001 (PE only)
  assert property ((rv==3'b001 && pe_s inside {2'b00,2'b01}) |-> ##0
                   (r2pe_ack && west_cfg_bundle==MUX_PE && south_cfg_bundle==MUX_NULL && pe_cfg_bundle==PE_NULL));
  assert property ((rv==3'b001 && pe_s==2'b10) |-> ##0
                   (r2pe_ack && south_cfg_bundle==MUX_PE && west_cfg_bundle==MUX_NULL && pe_cfg_bundle==PE_NULL));
  assert property ((rv==3'b001 && pe_s==2'b11) |-> ##0
                   (!r2pe_ack && south_cfg_bundle==MUX_NULL && west_cfg_bundle==MUX_NULL && pe_cfg_bundle==PE_NULL));

  // rv == 010 (NORTH only)
  assert property ((rv==3'b010 && n_s inside {2'b00,2'b01}) |-> ##0
                   (!r2pe_ack && west_cfg_bundle==MUX_NORTH && south_cfg_bundle==MUX_NULL && pe_cfg_bundle==PE_NULL));
  assert property ((rv==3'b010 && n_s==2'b10) |-> ##0
                   (!r2pe_ack && south_cfg_bundle==MUX_NORTH && west_cfg_bundle==MUX_NULL && pe_cfg_bundle==PE_NULL));
  assert property ((rv==3'b010 && n_s==2'b11) |-> ##0
                   (!r2pe_ack && pe_cfg_bundle==PE_NORTH && west_cfg_bundle==MUX_NULL && south_cfg_bundle==MUX_NULL));

  // rv == 011 (PE + NORTH)
  assert property ((rv==3'b011 && n_s inside {2'b00,2'b01}) |-> ##0
                   (r2pe_ack && west_cfg_bundle==MUX_NORTH && south_cfg_bundle==MUX_PE && pe_cfg_bundle==PE_NULL));
  assert property ((rv==3'b011 && n_s==2'b10) |-> ##0
                   (r2pe_ack && south_cfg_bundle==MUX_NORTH && west_cfg_bundle==MUX_PE && pe_cfg_bundle==PE_NULL));
  assert property ((rv==3'b011 && n_s==2'b11) |-> ##0
                   (r2pe_ack && west_cfg_bundle==MUX_PE && pe_cfg_bundle==PE_NORTH && south_cfg_bundle==MUX_NULL));

  // rv == 100 (EAST only)
  assert property ((rv==3'b100 && e_s inside {2'b00,2'b01}) |-> ##0
                   (!r2pe_ack && west_cfg_bundle==MUX_EAST && south_cfg_bundle==MUX_NULL && pe_cfg_bundle==PE_NULL));
  assert property ((rv==3'b100 && e_s==2'b10) |-> ##0
                   (!r2pe_ack && south_cfg_bundle==MUX_EAST && west_cfg_bundle==MUX_NULL && pe_cfg_bundle==PE_NULL));
  assert property ((rv==3'b100 && e_s==2'b11) |-> ##0
                   (!r2pe_ack && pe_cfg_bundle==PE_EAST && west_cfg_bundle==MUX_NULL && south_cfg_bundle==MUX_NULL));

  // rv == 101 (PE + EAST)
  assert property ((rv==3'b101 && e_s inside {2'b00,2'b01}) |-> ##0
                   (r2pe_ack && west_cfg_bundle==MUX_EAST && south_cfg_bundle==MUX_PE && pe_cfg_bundle==PE_NULL));
  assert property ((rv==3'b101 && e_s==2'b10) |-> ##0
                   (r2pe_ack && south_cfg_bundle==MUX_EAST && west_cfg_bundle==MUX_PE && pe_cfg_bundle==PE_NULL));
  assert property ((rv==3'b101 && e_s==2'b11) |-> ##0
                   (r2pe_ack && west_cfg_bundle==MUX_PE && pe_cfg_bundle==PE_EAST && south_cfg_bundle==MUX_NULL));

  // rv == 110 (EAST + NORTH)
  assert property ((rv==3'b110 && e_s inside {2'b00,2'b01}) |-> ##0
                   (!r2pe_ack && west_cfg_bundle==MUX_EAST && south_cfg_bundle==MUX_NORTH && pe_cfg_bundle==PE_NULL));
  assert property ((rv==3'b110 && e_s==2'b10) |-> ##0
                   (!r2pe_ack && south_cfg_bundle==MUX_EAST && west_cfg_bundle==MUX_NORTH && pe_cfg_bundle==PE_NULL));
  assert property ((rv==3'b110 && e_s==2'b11) |-> ##0
                   (!r2pe_ack && west_cfg_bundle==MUX_NORTH && pe_cfg_bundle==PE_EAST && south_cfg_bundle==MUX_NULL));

  // rv == 111 (EAST + NORTH + PE)
  assert property ((rv==3'b111 && e_s==2'b00) |-> ##0
                   (!r2pe_ack && west_cfg_bundle==MUX_EAST && south_cfg_bundle==MUX_NORTH && pe_cfg_bundle==PE_NULL));

  assert property ((rv==3'b111 && e_s==2'b01 && n_s==2'b11) |-> ##0
                   (r2pe_ack && west_cfg_bundle==MUX_EAST && south_cfg_bundle==MUX_PE && pe_cfg_bundle==PE_NORTH));
  assert property ((rv==3'b111 && e_s==2'b01 && n_s!=2'b11) |-> ##0
                   (!r2pe_ack && west_cfg_bundle==MUX_EAST && south_cfg_bundle==MUX_NORTH && pe_cfg_bundle==PE_NULL));

  assert property ((rv==3'b111 && e_s==2'b10 && n_s==2'b11) |-> ##0
                   (r2pe_ack && west_cfg_bundle==MUX_PE && south_cfg_bundle==MUX_NULL && pe_cfg_bundle==PE_NORTH));
  assert property ((rv==3'b111 && e_s==2'b10 && n_s!=2'b11) |-> ##0
                   (!r2pe_ack && west_cfg_bundle==MUX_NORTH && south_cfg_bundle==MUX_EAST && pe_cfg_bundle==PE_NULL));

  assert property ((rv==3'b111 && e_s==2'b11 && n_s==2'b01) |-> ##0
                   (r2pe_ack && west_cfg_bundle==MUX_NORTH && south_cfg_bundle==MUX_PE && pe_cfg_bundle==PE_EAST));
  assert property ((rv==3'b111 && e_s==2'b11 && n_s!=2'b01) |-> ##0
                   (r2pe_ack && west_cfg_bundle==MUX_PE && south_cfg_bundle==MUX_NORTH && pe_cfg_bundle==PE_EAST));

  // Structural invariants
  assert property (1 |-> ##0 !((west_cfg_bundle==MUX_PE) && (south_cfg_bundle==MUX_PE)));

  // Functional coverage (concise, behavior-oriented)
  cover property (rv==3'b000);
  cover property (rv==3'b001 && pe_s==2'b00);
  cover property (rv==3'b001 && pe_s==2'b01);
  cover property (rv==3'b001 && pe_s==2'b10);
  cover property (rv==3'b001 && pe_s==2'b11);

  cover property (rv==3'b010 && n_s==2'b00);
  cover property (rv==3'b010 && n_s==2'b10);
  cover property (rv==3'b010 && n_s==2'b11);

  cover property (rv==3'b100 && e_s==2'b00);
  cover property (rv==3'b100 && e_s==2'b10);
  cover property (rv==3'b100 && e_s==2'b11);

  cover property (rv==3'b011 && n_s==2'b10);
  cover property (rv==3'b011 && n_s==2'b11);

  cover property (rv==3'b101 && e_s==2'b10);
  cover property (rv==3'b101 && e_s==2'b11);

  cover property (rv==3'b110 && e_s==2'b10);
  cover property (rv==3'b110 && e_s==2'b11);

  cover property (rv==3'b111 && e_s==2'b00);
  cover property (rv==3'b111 && e_s==2'b01 && n_s==2'b11);
  cover property (rv==3'b111 && e_s==2'b01 && n_s!=2'b11);
  cover property (rv==3'b111 && e_s==2'b10 && n_s==2'b11);
  cover property (rv==3'b111 && e_s==2'b10 && n_s!=2'b11);
  cover property (rv==3'b111 && e_s==2'b11 && n_s==2'b01);
  cover property (rv==3'b111 && e_s==2'b11 && n_s!=2'b01);

  // Ack coverage
  cover property (rv inside {3'b001,3'b011,3'b101,3'b111} && ##0 r2pe_ack);
  cover property (rv inside {3'b000,3'b010,3'b100,3'b110} && ##0 !r2pe_ack);

endmodule

bind arbitro arbitro_sva sva_i (
  .pe_request_bundle(pe_request_bundle),
  .north_request_bundle(north_request_bundle),
  .east_request_bundle(east_request_bundle),
  .pe_cfg_bundle(pe_cfg_bundle),
  .south_cfg_bundle(south_cfg_bundle),
  .west_cfg_bundle(west_cfg_bundle),
  .r2pe_ack(r2pe_ack)
);