// SVA for control_enable_options
// Bind this module to the DUT. Focuses on reset, write, readback, bus driving, and bit-mapping.

module control_enable_options_sva
  #(parameter bit [7:0] DEVOPTIONS = 8'h0E,
              bit [7:0] DEVOPTS2   = 8'h0F)
(
  input  logic        clk,
  input  logic        rst_n,
  input  logic [7:0]  zxuno_addr,
  input  logic        zxuno_regrd,
  input  logic        zxuno_regwr,
  input  logic [7:0]  din,
  input  logic [7:0]  dout,
  input  logic        oe_n,
  input  logic        disable_ay,
  input  logic        disable_turboay,
  input  logic        disable_7ffd,
  input  logic        disable_1ffd,
  input  logic        disable_romsel7f,
  input  logic        disable_romsel1f,
  input  logic        enable_timexmmu,
  input  logic        disable_spisd,
  input  logic        disable_timexscr,
  input  logic        disable_ulaplus,
  input  logic        disable_radas
);

  // Expected mirror of registers (scoreboard)
  logic [7:0] exp_devoptions, exp_devopts2;

  // Decode helpers
  wire wr_devoptions  = zxuno_regwr && (zxuno_addr == DEVOPTIONS);
  wire wr_devopts2    = zxuno_regwr && (zxuno_addr == DEVOPTS2);
  wire rd_devoptions  = zxuno_regrd && (zxuno_addr == DEVOPTIONS);
  wire rd_devopts2    = zxuno_regrd && (zxuno_addr == DEVOPTS2);
  wire rd_any_valid   = rd_devoptions || rd_devopts2;

  // Scoreboard model of DUT state
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      exp_devoptions <= '0;
      exp_devopts2   <= '0;
    end else if (wr_devoptions) begin
      exp_devoptions <= din;
    end else if (wr_devopts2) begin
      exp_devopts2   <= din;
    end
  end

  // Default clocking
  default clocking cb @(posedge clk); endclocking

  // 1) Reset drives registers to 0 (observable via outputs)
  assert property ( !rst_n |=> (disable_ay==0 && disable_turboay==0 && disable_7ffd==0 &&
                                disable_1ffd==0 && disable_romsel7f==0 && disable_romsel1f==0 &&
                                enable_timexmmu==0 && disable_spisd==0 &&
                                disable_timexscr==0 && disable_ulaplus==0 && disable_radas==0) )
    else $error("Reset did not clear option outputs to 0");

  // 2) Bit mapping from DEVOPTIONS to outputs (continuous)
  // Pack outputs into vector to compare against expected register mirror
  wire [7:0] map_devoptions = {disable_spisd, enable_timexmmu, disable_romsel1f, disable_romsel7f,
                               disable_1ffd,  disable_7ffd,   disable_turboay,  disable_ay};

  assert property ( disable iff (!rst_n) map_devoptions == exp_devoptions )
    else $error("DEVOPTIONS output bit mapping mismatch");

  // And DEVOPTS2 lower bits mapping
  assert property ( disable iff (!rst_n) disable_timexscr == exp_devopts2[0] )
    else $error("DEVOPTS2[0] -> disable_timexscr mismatch");
  assert property ( disable iff (!rst_n) disable_ulaplus  == exp_devopts2[1] )
    else $error("DEVOPTS2[1] -> disable_ulaplus mismatch");
  assert property ( disable iff (!rst_n) disable_radas    == exp_devopts2[2] )
    else $error("DEVOPTS2[2] -> disable_radas mismatch");

  // 3) Write updates are reflected next cycle on mapped outputs
  assert property ( disable iff (!rst_n)
                    wr_devoptions |=> (map_devoptions == $past(din)) )
    else $error("Write to DEVOPTIONS not reflected on outputs next cycle");

  assert property ( disable iff (!rst_n)
                    wr_devopts2 |=> ({disable_radas,disable_ulaplus,disable_timexscr} == $past(din[2:0])) )
    else $error("Write to DEVOPTS2 not reflected on outputs next cycle");

  // 4) Read bus behavior: oe_n low exactly on valid reads; dout selected correctly
  // oe_n equivalence
  assert property ( disable iff (!rst_n) (oe_n == 1'b0) <-> rd_any_valid )
    else $error("oe_n not consistent with read decode");

  // Data muxing
  assert property ( disable iff (!rst_n) rd_devoptions |-> (dout == exp_devoptions && oe_n==1'b0) )
    else $error("Read DEVOPTIONS returned wrong data");
  assert property ( disable iff (!rst_n) rd_devopts2   |-> (dout == exp_devopts2   && oe_n==1'b0) )
    else $error("Read DEVOPTS2 returned wrong data");

  // Default bus drive when not a valid read
  assert property ( disable iff (!rst_n)
                    !rd_any_valid |-> (oe_n==1'b1 && dout==8'hFF) )
    else $error("Bus default drive (oe_n/dout) incorrect when not reading valid addr");

  // 5) X/Z sanitization after reset release
  assert property ( disable iff (!rst_n)
                    !$isunknown({oe_n, dout,
                                 disable_ay, disable_turboay, disable_7ffd, disable_1ffd,
                                 disable_romsel7f, disable_romsel1f, enable_timexmmu, disable_spisd,
                                 disable_timexscr, disable_ulaplus, disable_radas}) )
    else $error("X/Z detected on outputs");

  // 6) Functional readback persistence: last written value is returned until next write/reset
  // DEVOPTIONS
  property devoptions_readback_holds;
    logic [7:0] v;
    (wr_devoptions, v = din)
      |->
      ( (!wr_devoptions && rst_n) [*0:$] ##1 rd_devoptions |-> (dout == v) )
      throughout (rst_n && !wr_devoptions);
  endproperty
  assert property ( disable iff (!rst_n) devoptions_readback_holds )
    else $error("DEVOPTIONS readback did not hold last written value");

  // DEVOPTS2
  property devopts2_readback_holds;
    logic [7:0] v;
    (wr_devopts2, v = din)
      |->
      ( (!wr_devopts2 && rst_n) [*0:$] ##1 rd_devopts2 |-> (dout == v) )
      throughout (rst_n && !wr_devopts2);
  endproperty
  assert property ( disable iff (!rst_n) devopts2_readback_holds )
    else $error("DEVOPTS2 readback did not hold last written value");

  // 7) Coverage: writes, reads, and readback
  cover property ( wr_devoptions );
  cover property ( wr_devopts2 );
  cover property ( rd_devoptions );
  cover property ( rd_devopts2 );

  // Write->Readback cover (DEVOPTIONS)
  cover property ( (wr_devoptions, $past(din)) ##[1:10] rd_devoptions && (dout == exp_devoptions) );
  // Write->Readback cover (DEVOPTS2)
  cover property ( (wr_devopts2, $past(din)) ##[1:10] rd_devopts2 && (dout == exp_devopts2) );

  // Bit toggle coverage (any of the option outputs toggles)
  cover property ( disable iff (!rst_n) $rose(disable_ay) or $fell(disable_ay) );
  cover property ( disable iff (!rst_n) $rose(disable_timexscr) or $fell(disable_timexscr) );

endmodule

// Bind into DUT; parameters are taken from the DUT instance
bind control_enable_options control_enable_options_sva
  #(.DEVOPTIONS(DEVOPTIONS), .DEVOPTS2(DEVOPTS2)) 
  control_enable_options_sva_i
  (
    .clk(clk),
    .rst_n(rst_n),
    .zxuno_addr(zxuno_addr),
    .zxuno_regrd(zxuno_regrd),
    .zxuno_regwr(zxuno_regwr),
    .din(din),
    .dout(dout),
    .oe_n(oe_n),
    .disable_ay(disable_ay),
    .disable_turboay(disable_turboay),
    .disable_7ffd(disable_7ffd),
    .disable_1ffd(disable_1ffd),
    .disable_romsel7f(disable_romsel7f),
    .disable_romsel1f(disable_romsel1f),
    .enable_timexmmu(enable_timexmmu),
    .disable_spisd(disable_spisd),
    .disable_timexscr(disable_timexscr),
    .disable_ulaplus(disable_ulaplus),
    .disable_radas(disable_radas)
  );