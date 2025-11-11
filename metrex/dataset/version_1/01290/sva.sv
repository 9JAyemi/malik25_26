// SVA for pram_sram_ctrl
// Bind this file to the DUT. Focused, high-quality assertions + key coverage.

`ifndef PRAM_SRAM_CTRL_SVA
`define PRAM_SRAM_CTRL_SVA

module pram_sram_ctrl_sva (
  input  logic        clk,
  input  logic        clr,
  input  logic        go,
  input  logic        halt,
  input  logic        we,
  input  logic        en,
  input  logic [17:0] sram_addr,
  input  logic [5:0]  pattern,
  input  logic [2:0]  state,
  input  logic [17:0] addrv,
  input  logic [5:0]  patternv
);

  localparam [2:0]
    START       = 3'b000,
    ADDROUT     = 3'b001,
    TEST1       = 3'b010,
    WAIT_AND_GO = 3'b011,
    READ        = 3'b100,
    TEST2       = 3'b101,
    HALT        = 3'b110;

  default clocking cb @(posedge clk); endclocking
  default disable iff (clr);

  // Basic invariants
  assert property (state inside {START,ADDROUT,TEST1,WAIT_AND_GO,READ,TEST2,HALT});
  assert property (sram_addr == addrv);
  assert property (pattern   == patternv);

  // WE mapping to states
  assert property (state inside {START,ADDROUT,WAIT_AND_GO,READ,TEST2} |-> we==1);
  assert property (state inside {TEST1,HALT}                          |-> we==0);

  // Next-state and datapath behavior
  assert property (state==START   &&  go                 |=> state==ADDROUT && en==1 && we==1 && addrv==0);
  assert property (state==START   && !go                 |=> state==START);

  assert property (state==ADDROUT                        |=> state==TEST1 && we==1);

  assert property (state==TEST1   &&  halt               |=> state==HALT);
  assert property (state==TEST1   && !halt && addrv!=18'h3FFFF |=> state==ADDROUT    && addrv == $past(addrv)+1);
  assert property (state==TEST1   && !halt && addrv==18'h3FFFF |=> state==WAIT_AND_GO && addrv == 18'h0 && en==0);

  assert property (state==WAIT_AND_GO &&  go             |=> state==WAIT_AND_GO);
  assert property (state==WAIT_AND_GO && !go             |=> state==READ);

  assert property (state==READ    &&  go                 |=> state==TEST2 && addrv == $past(addrv)+1);
  assert property (state==READ    && !go                 |=> state==READ);

  assert property (state==TEST2   && addrv!=18'h0        |=> state==WAIT_AND_GO);
  assert property (state==TEST2   && addrv==18'h0        |=> state==START && patternv == $past(patternv)+1);

  assert property (state==HALT                           |=> state==HALT);

  // Change-only-when-expected checks
  assert property ($changed(en)      |-> (($past(state)==START && $past(go)) ||
                                         ($past(state)==TEST1 && !$past(halt) && $past(addrv)==18'h3FFFF)));
  assert property ($changed(addrv)   |-> (($past(state)==START && $past(go)) ||
                                         ($past(state)==TEST1 && !$past(halt)) ||
                                         ($past(state)==READ  && $past(go))));
  assert property ($changed(patternv)|-> ( $past(state)==TEST2 && $past(addrv)==18'h0 ));

  // Key coverpoints
  cover property (state==TEST1 && !halt && addrv==18'h3FFFF ##1 state==WAIT_AND_GO && addrv==18'h0 && en==0);
  cover property (state==READ && go ##1 state==TEST2);
  cover property (state==TEST2 && addrv==18'h0 ##1 state==START);
  cover property (state==TEST1 && halt ##1 state==HALT);

endmodule

// Bind to DUT (connects to internals by name)
bind pram_sram_ctrl pram_sram_ctrl_sva sva_i(
  .clk(clk), .clr(clr), .go(go), .halt(halt),
  .we(we), .en(en), .sram_addr(sram_addr), .pattern(pattern),
  .state(state), .addrv(addrv), .patternv(patternv)
);

`endif