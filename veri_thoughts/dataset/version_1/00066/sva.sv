// SVA bind module for vga_output
// Concise, high-quality checks and coverage of counters, syncs, and color

module vga_output_sva (
  input  logic        clk,
  input  logic        vga_hs,
  input  logic        vga_vs,
  input  logic [4:0]  vga_r,
  input  logic [5:0]  vga_g,
  input  logic [4:0]  vga_b,
  input  logic [10:0] h_counter,
  input  logic [9:0]  v_counter
);
  // Derived constants from DUT
  localparam int H_TOTAL    = 640+96+16+48;   // 800
  localparam int V_TOTAL    = 480+2+10+33;    // 525
  localparam int HS_START   = 640+16;         // 656
  localparam int HS_END     = HS_START + 96 - 1;   // 751
  localparam int VS_START   = 480+10;         // 490
  localparam int VS_END     = VS_START + 2 - 1;    // 491
  localparam int WHITE_START= HS_START;       // 656
  localparam int WHITE_END  = WHITE_START + 8 - 1; // 663

  logic past_valid;
  initial past_valid = 0;
  always_ff @(posedge clk) past_valid <= 1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid || $isunknown({h_counter,v_counter}));

  // Counter range
  assert property (h_counter < H_TOTAL);
  assert property (v_counter < V_TOTAL);

  // Counter increment and wrap
  assert property ($past(h_counter) != H_TOTAL-1 |-> h_counter == $past(h_counter)+1);
  assert property ($past(h_counter) == H_TOTAL-1 |-> h_counter == 0);

  assert property ($past(v_counter) != V_TOTAL-1 |-> v_counter == $past(v_counter)+1);
  assert property ($past(v_counter) == V_TOTAL-1 |-> v_counter == 0);

  // Sync polarity and windows (active low)
  assert property ( (h_counter inside {[HS_START:HS_END]}) |-> (vga_hs == 1'b0) );
  assert property ( !(h_counter inside {[HS_START:HS_END]}) |-> (vga_hs == 1'b1) );

  assert property ( (v_counter inside {[VS_START:VS_END]}) |-> (vga_vs == 1'b0) );
  assert property ( !(v_counter inside {[VS_START:VS_END]}) |-> (vga_vs == 1'b1) );

  // Color generation: white in early HSYNC region, black otherwise
  assert property ( (h_counter inside {[WHITE_START:WHITE_END]})
                    |-> (vga_r==5'd31 && vga_g==6'd63 && vga_b==5'd31) );

  assert property ( !(h_counter inside {[WHITE_START:WHITE_END]})
                    |-> (vga_r==5'd0  && vga_g==6'd0  && vga_b==5'd0 ) );

  // White region must coincide with HS low
  assert property ( (h_counter inside {[WHITE_START:WHITE_END]}) |-> (vga_hs==1'b0) );

  // No X/Z on outputs when counters are known
  assert property ( !$isunknown({vga_hs, vga_vs, vga_r, vga_g, vga_b}) );

  // Coverage
  cover property (h_counter==H_TOTAL-1 ##1 h_counter==0);
  cover property (v_counter==V_TOTAL-1 ##1 v_counter==0);

  cover property (h_counter==HS_START && vga_hs==0);
  cover property (h_counter==HS_END   && vga_hs==0 ##1 vga_hs==1);

  cover property (v_counter==VS_START && vga_vs==0);
  cover property (v_counter==VS_END   && vga_vs==0 ##1 vga_vs==1);

  cover property (h_counter==WHITE_START && vga_r==31 && vga_g==63 && vga_b==31);
  cover property (h_counter==WHITE_END   && vga_r==31 && vga_g==63 && vga_b==31 ##1 vga_r==0 && vga_g==0 && vga_b==0);
endmodule

bind vga_output vga_output_sva sva_i (
  .clk(clk),
  .vga_hs(vga_hs),
  .vga_vs(vga_vs),
  .vga_r(vga_r),
  .vga_g(vga_g),
  .vga_b(vga_b),
  .h_counter(h_counter),
  .v_counter(v_counter)
);