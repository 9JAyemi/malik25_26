// SVA for BRAM1: concise, high-quality checks and coverage
module BRAM1_sva #(
  parameter int PIPELINED  = 0,
  parameter int ADDR_WIDTH = 1,
  parameter int DATA_WIDTH = 1,
  parameter int MEMSIZE    = 1
)(
  input  logic                       CLK,
  input  logic                       EN,
  input  logic                       WE,
  input  logic [ADDR_WIDTH-1:0]      ADDR,
  input  logic [DATA_WIDTH-1:0]      DI,
  input  logic [DATA_WIDTH-1:0]      DO
);
  // Parameter sanity
  initial begin
    assert (MEMSIZE > 0) else $fatal("MEMSIZE must be > 0");
    assert (MEMSIZE <= (1<<ADDR_WIDTH))
      else $fatal("MEMSIZE exceeds addressable space by ADDR_WIDTH");
  end

  // Simple golden model (only for addresses written since start)
  logic [DATA_WIDTH-1:0] mm [0:MEMSIZE-1];
  bit                    kn [0:MEMSIZE-1];

  always_ff @(posedge CLK) begin
    if (EN && WE) begin
      mm[$unsigned(ADDR)] <= DI;
      kn[$unsigned(ADDR)] <= 1'b1;
    end
  end

  default clocking cb @(posedge CLK); endclocking

  // Address range when enabled
  assert property ( EN |-> $unsigned(ADDR) < MEMSIZE )
    else $error("ADDR out of range when EN=1");

  // Next-cycle DO behavior: write-first and read timing (1-cycle latency externally)
  assert property (
    EN |=> ( $past(WE)
             ? DO == $past(DI)
             : ( ($unsigned($past(ADDR)) < MEMSIZE && kn[$unsigned($past(ADDR))])
                 ? DO == $past(mm[$unsigned($past(ADDR))])
                 : 1'b1 ) )
  ) else $error("DO mismatch on next cycle");

  // DO holds when disabled
  assert property ( !EN |=> DO == $past(DO) )
    else $error("DO changed while EN=0");

  // No X/Z on valid next-cycle DO after a write or a read of known location
  assert property (
    ($past(EN) && ( $past(WE)
                  || (($unsigned($past(ADDR)) < MEMSIZE) && kn[$unsigned($past(ADDR))]) ))
    |-> !$isunknown(DO)
  ) else $error("DO is X/Z on valid cycle");

  // No glitches between clocks (DO only updates on posedge)
  assert property (@(negedge CLK) $stable(DO))
    else $error("DO changed away from posedge");

  // Functional coverage
  cover property ( EN && WE );                                         // any write
  cover property ( EN && !WE && ($unsigned(ADDR)<MEMSIZE) );           // any read
  cover property ( EN && WE && ($unsigned(ADDR)==0) );                 // write first addr
  cover property ( EN && WE && ($unsigned(ADDR)==MEMSIZE-1) );         // write last addr
  cover property ( EN && WE ##1 EN && !WE && ($past(ADDR)==ADDR) );    // write then read same addr
  cover property ( !EN ##1 !EN );                                      // disabled hold
  cover property ( PIPELINED==0 );                                     // instance is non-pipelined
  cover property ( PIPELINED==1 );                                     // instance is pipelined
endmodule

// Bind into DUT
bind BRAM1 BRAM1_sva #(
  .PIPELINED (PIPELINED),
  .ADDR_WIDTH(ADDR_WIDTH),
  .DATA_WIDTH(DATA_WIDTH),
  .MEMSIZE   (MEMSIZE)
) bram1_sva_i (
  .CLK (CLK),
  .EN  (EN),
  .WE  (WE),
  .ADDR(ADDR),
  .DI  (DI),
  .DO  (DO)
);