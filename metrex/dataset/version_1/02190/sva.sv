// SVA checker + bind for blk_mem_gen_0blk_mem_gen_v8_2_synth
// Focus: protocol, data integrity via scoreboard, and concise coverage.

module blk_mem_gen_0blk_mem_gen_v8_2_synth_sva
(
  input  logic         clkb,
  input  logic         enb,
  input  logic         wea,
  input  logic         clka,
  input  logic [8:0]   addrb,
  input  logic [8:0]   addra,
  input  logic [63:0]  dina,
  input  logic [63:0]  doutb
);

  // Derive widths/limits from ports
  localparam int AW = $bits(addra);
  localparam int DW = $bits(doutb);
  localparam int DEPTH = 1 << AW;
  localparam logic [AW-1:0] MIN_ADDR = '0;
  localparam logic [AW-1:0] MAX_ADDR = {AW{1'b1}};

  // Past-valid for disable iff
  bit past_valid;
  always_ff @(posedge clkb) past_valid <= 1'b1;

  // Simple scoreboard for last written data per address (via DUT interface)
  logic [DW-1:0] sb [0:DEPTH-1];
  bit            sb_valid [0:DEPTH-1];

  always_ff @(posedge clkb) begin
    if (past_valid && enb && wea && !$isunknown({clka,addra,addrb})) begin
      sb[clka ? addra : addrb]      <= dina;
      sb_valid[clka ? addra : addrb] <= 1'b1;
    end
  end

  default clocking cb @(posedge clkb); endclocking
  default disable iff (!past_valid);

  // Control/inputs must be known when enabled
  assert property (enb |-> !$isunknown({wea,clka,addra,addrb}))
    else $error("Unknown control/address while enb=1");
  assert property (enb && wea |-> !$isunknown(dina))
    else $error("Unknown dina on write");

  // Output update/stability rules
  //  - doutb updates only on read cycles
  assert property ($changed(doutb) |-> $past(enb && !wea))
    else $error("doutb changed without a read cycle");
  //  - when not reading, doutb holds its value (includes write or enb=0)
  assert property (!(enb && !wea) |=> doutb == $past(doutb))
    else $error("doutb not stable when no read");

  // Functional data check using scoreboard:
  //  - 1-cycle read latency, and data matches last written value to that address (if known)
  assert property ( (enb && !wea) && sb_valid[$past(clka ? addra : addrb)]
                    |=> doutb == sb[$past(clka ? addra : addrb)] )
    else $error("Read data mismatch with last written value");

  // Lightweight coverage
  // Cover both address-select paths on write and read
  cover property (enb && wea &&  clka); // write via addra
  cover property (enb && wea && !clka); // write via addrb
  cover property (enb && !wea &&  clka); // read via addra
  cover property (enb && !wea && !clka); // read via addrb

  // Boundary address coverage (writes)
  cover property (enb && wea && clka && addra == MIN_ADDR);
  cover property (enb && wea && clka && addra == MAX_ADDR);
  cover property (enb && wea && !clka && addrb == MIN_ADDR);
  cover property (enb && wea && !clka && addrb == MAX_ADDR);

  // Write -> Read same address within a few cycles (exercise latency and data path)
  sequence wr_s(addr_t, data_t);
    (enb && wea, addr_t = (clka ? addra : addrb), data_t = dina);
  endsequence
  logic [AW-1:0] A;
  logic [DW-1:0] D;
  cover property ( wr_s(A,D) ##[1:5] (enb && !wea && ((clka ? addra : addrb) == A)) ##1 (doutb == D) );

  // Exercise enable low
  cover property (!enb);

endmodule

// Bind into all instances of the DUT
bind blk_mem_gen_0blk_mem_gen_v8_2_synth
  blk_mem_gen_0blk_mem_gen_v8_2_synth_sva sva_i
  (
    .clkb(clkb),
    .enb(enb),
    .wea(wea),
    .clka(clka),
    .addrb(addrb),
    .addra(addra),
    .dina(dina),
    .doutb(doutb)
  );