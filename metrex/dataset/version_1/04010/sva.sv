// SVA for control_interface
// Bind this module to the DUT instance. Focused, high-quality checks and coverage.

module control_interface_sva #(
  parameter int ASIZE    = 16,
  parameter int REF_PER  = 8192, // for coverage only
  parameter int INIT_PER = 1000  // for coverage only
)(
  input logic                CLK,
  input logic                RESET_N,
  input logic [2:0]          CMD,
  input logic [ASIZE-1:0]    ADDR,
  input logic                REF_ACK,
  input logic                INIT_ACK,   // unused by DUT, kept for port match
  input logic                CM_ACK,
  input logic                NOP,
  input logic                READA,
  input logic                WRITEA,
  input logic                REFRESH,
  input logic                PRECHARGE,
  input logic                LOAD_MODE,
  input logic [ASIZE-1:0]    SADDR,
  input logic                REF_REQ,
  input logic                INIT_REQ,
  input logic                CMD_ACK
);

  default clocking cb @(posedge CLK); endclocking
  default disable iff (!RESET_N)

  // Known/clean outputs when out of reset
  assert property (!$isunknown({NOP,READA,WRITEA,REFRESH,PRECHARGE,LOAD_MODE,REF_REQ,INIT_REQ,CMD_ACK,SADDR})));

  // Reset values
  assert property (@(posedge CLK) !RESET_N |-> (NOP==0 && READA==0 && WRITEA==0 &&
                                                REFRESH==0 && PRECHARGE==0 && LOAD_MODE==0 &&
                                                REF_REQ==0 && INIT_REQ==0 && CMD_ACK==0 && SADDR=='0));

  // Registered address follows ADDR (1-cycle latency)
  assert property (SADDR == $past(ADDR));

  // Command decode is 1-cycle delayed and mutually exclusive
  assert property (NOP     == ($past(CMD)==3'b000));
  assert property (READA   == ($past(CMD)==3'b001));
  assert property (WRITEA  == ($past(CMD)==3'b010));
  assert property (!( (NOP && READA) || (NOP && WRITEA) || (READA && WRITEA) ));

  // CMD_ACK: 1-cycle pulse on CM_ACK high, and only when CM_ACK is high
  assert property ($rose(CM_ACK) |-> CMD_ACK);
  assert property (CMD_ACK |-> CM_ACK);
  assert property ($rose(CMD_ACK) |-> ##1 !CMD_ACK);

  // INIT_REQ behavior
  assert property ($rose(RESET_N) |-> INIT_REQ);            // goes high immediately after reset release
  assert property ($fell(INIT_REQ) |-> !INIT_REQ[*]);       // once it falls, it never re-asserts
  assert property (INIT_REQ |-> (!REFRESH && !PRECHARGE && !LOAD_MODE)); // no other init ops during INIT_REQ

  // Initialization schedule relative to INIT_REQ falling edge:
  // PRECHARGE @ +20, REFRESH @ +40,+60,...,+180, LOAD_MODE @ +200; all are 1-cycle pulses
  assert property ($fell(INIT_REQ) |-> ##20  PRECHARGE ##1 !PRECHARGE);
  for (genvar k=0; k<8; k++) begin : gen_ref_init_pulses
    localparam int O = 40 + 20*k;
    assert property ($fell(INIT_REQ) |-> ##O REFRESH ##1 !REFRESH);
  end
  assert property ($fell(INIT_REQ) |-> ##200 LOAD_MODE ##1 !LOAD_MODE);

  // No overlap among init control outputs
  assert property (!(REFRESH && PRECHARGE) && !(REFRESH && LOAD_MODE) && !(PRECHARGE && LOAD_MODE));

  // Refresh request generation constraints
  assert property (INIT_REQ |-> !REF_REQ);                                // blocked during init
  assert property ((REF_ACK || INIT_REQ) |-> !REF_REQ);                   // cleared same cycle as ACK or INIT_REQ
  assert property ((REF_REQ && !REF_ACK && !INIT_REQ) |=> REF_REQ);       // sticky until cleared

  // Optional: REF_REQ cannot glitch low then high without an intervening clear
  assert property ($fell(REF_REQ) |-> (REF_ACK || INIT_REQ || !RESET_N)); // only falls when cleared

  // -----------------------
  // Coverage
  // -----------------------

  // See each decode output asserted at least once
  cover property (NOP);
  cover property (READA);
  cover property (WRITEA);

  // Address pipeline observed
  cover property ($changed(ADDR) ##1 (SADDR == $past(ADDR)));

  // CMD_ACK pulse observed
  cover property ($rose(CM_ACK) && CMD_ACK);

  // REF_REQ/REF_ACK handshake observed
  cover property ($rose(REF_REQ) ##[1:$] REF_ACK);

  // INIT_REQ length observed to be at least INIT_PER cycles (not a check, just coverage)
  cover property ($rose(RESET_N) ##1 INIT_REQ[*INIT_PER]);

  // Full init sequence: PRECHARGE, 8x REFRESH (20-cycle spacing), LOAD_MODE
  sequence s_ref8_20; (##20 (REFRESH ##1 !REFRESH))[*8]; endsequence
  cover property ($fell(INIT_REQ) ##20 (PRECHARGE ##1 !PRECHARGE) s_ref8_20 ##20 (LOAD_MODE ##1 !LOAD_MODE));

  // Toggle of INIT_ACK (unused input) for completeness
  cover property ($changed(INIT_ACK));

endmodule

// Bind example (adjust instance path/names as needed):
// bind control_interface control_interface_sva #(.ASIZE(ASIZE), .REF_PER(8192), .INIT_PER(1000)) ci_sva_i (.*);