// SVA for MemoryCtrl
// Bind into DUT to access internals for precise checks/timing
module MemoryCtrl_sva (
  input  logic             Clk, Reset,
  input  logic             BtnU_Pulse, BtnD_Pulse,
  input  logic [22:0]      AddressIn,
  input  logic [26:1]      MemAdr,
  input  logic             MemOE, MemWR, RamCS, RamUB, RamLB, RamAdv, RamCRE,
  input  logic             writeData,
  // internals
  input  logic [7:0]       state,
  input  logic [6:0]       clock_counter,
  input  logic [22:0]      address
);
  // Mirror DUT encodings
  localparam logic [7:0]
    INITIAL_CONFIG = 8'b0000_0001,
    CONFIGMEM      = 8'b0000_0010,
    CONFIGMEM2     = 8'b0000_0100,
    INIT           = 8'b0000_1000,
    PREPARE_READ   = 8'b0001_0000,
    WAIT_S         = 8'b0010_0000,
    READ_DATA      = 8'b0100_0000,
    IDLE           = 8'b1000_0000;

  localparam logic [22:0] CONFIG_ADDR = 23'b000_10_00_0_1_011_1_0_0_0_0_01_1_111;

  default clocking cb @(posedge Clk); endclocking

  // Basic structural checks
  assert property (cb Reset |-> state == CONFIGMEM && writeData == 1'b0);
  assert property (cb disable iff (Reset) $onehot(state));
  assert property (cb MemAdr[26:23] == 4'b0000);
  assert property (cb {4'b0000, address} == MemAdr);
  assert property (cb disable iff (Reset) !$isunknown({MemAdr, MemOE, MemWR, RamCS, RamUB, RamLB, RamAdv, RamCRE, writeData}));

  // State transition timing and outputs (accounting for NBA semantics: check next-cycle effects)
  // CONFIGMEM -> CONFIGMEM2, outputs programmed and config address loaded
  assert property (cb state == CONFIGMEM |=> state == CONFIGMEM2
                   && RamCRE && !RamAdv && !RamCS && !MemWR && MemOE && RamUB && RamLB
                   && clock_counter == 7'd0
                   && MemAdr[22:0] == CONFIG_ADDR);

  // CONFIGMEM2 lasts exactly 3 cycles then INIT, and RamCS asserted upon leaving
  assert property (cb state == CONFIGMEM2 |=> ##3 (state == INIT && RamCS));

  // INIT -> PREPARE_READ; address captures AddressIn
  assert property (cb state == INIT |=> state == PREPARE_READ
                   && MemAdr[22:0] == $past(AddressIn));

  // PREPARE_READ -> WAIT; bus control settings
  assert property (cb state == PREPARE_READ |=> state == WAIT_S
                   && !RamCRE && !RamAdv && !RamCS && MemWR && MemOE && !RamUB && !RamLB
                   && clock_counter == 7'd0);

  // WAIT lasts exactly 4 cycles then READ_DATA; first READ_DATA cycle side-effects
  assert property (cb state == WAIT_S |=> ##4 (state == READ_DATA && writeData && !MemOE && RamAdv && clock_counter == 7'd0));

  // READ_DATA lasts exactly 128 cycles then IDLE; writeData clears in IDLE
  assert property (cb state == READ_DATA |=> ##128 (state == IDLE && !writeData));

  // IDLE hold/exit behavior and outputs
  assert property (cb (state == IDLE && !(BtnU_Pulse || BtnD_Pulse)) |=> state == IDLE);
  assert property (cb (state == IDLE &&  (BtnU_Pulse || BtnD_Pulse)) |=> state == CONFIGMEM);
  assert property (cb state == IDLE |=> !RamCRE && RamAdv && RamCS && MemWR && MemOE && RamUB && RamLB);

  // Protocol/style invariants
  assert property (cb MemOE == 1'b0 |-> state == READ_DATA);
  assert property (cb writeData |-> state == READ_DATA);
  assert property (cb state == READ_DATA |-> !RamUB && !RamLB);
  assert property (cb state == WAIT_S |-> RamAdv); // ADV high during WAIT

  // Functional coverage of key flows
  cover property (cb state == CONFIGMEM ##1 state == CONFIGMEM2 ##3 state == INIT ##1
                      state == PREPARE_READ ##4 state == READ_DATA ##128 state == IDLE);

  cover property (cb state == IDLE && BtnU_Pulse ##1 state == CONFIGMEM);
  cover property (cb state == IDLE && BtnD_Pulse ##1 state == CONFIGMEM);

endmodule

// Bind into DUT (example; adjust instance path as needed)
bind MemoryCtrl MemoryCtrl_sva sva_i (
  .Clk(Clk), .Reset(Reset),
  .BtnU_Pulse(BtnU_Pulse), .BtnD_Pulse(BtnD_Pulse),
  .AddressIn(AddressIn),
  .MemAdr(MemAdr),
  .MemOE(MemOE), .MemWR(MemWR), .RamCS(RamCS), .RamUB(RamUB), .RamLB(RamLB), .RamAdv(RamAdv), .RamCRE(RamCRE),
  .writeData(writeData),
  .state(state),
  .clock_counter(clock_counter),
  .address(address)
);