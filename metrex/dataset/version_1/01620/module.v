

module mig_7series_v4_0_poc_tap_base #
  (parameter MMCM_SAMP_WAIT             = 10,
   parameter POC_USE_METASTABLE_SAMP    = "FALSE",
   parameter TCQ                        = 100,
   parameter SAMPCNTRWIDTH              = 8,
   parameter SMWIDTH                    = 2,
   parameter TAPCNTRWIDTH               = 7,
   parameter TAPSPERKCLK                = 112)
  (
  psincdec, psen, run, run_end, run_too_small, run_polarity,
  samp_cntr, samps_hi, samps_hi_held, tap, sm, samps_zero, samps_one,
  pd_out, clk, samples, samps_solid_thresh, psdone, rst,
  poc_sample_pd
  );

  
  function integer clogb2 (input integer size); begin
      size = size - 1;
      for (clogb2=1; size>1; clogb2=clogb2+1)
            size = size >> 1;
    end
  endfunction input pd_out;
  input clk;
  input [SAMPCNTRWIDTH:0] samples, samps_solid_thresh;
  input psdone;
  input rst;

  localparam ONE = 1;

  localparam SAMP_WAIT_WIDTH = clogb2(MMCM_SAMP_WAIT);
  reg [SAMP_WAIT_WIDTH-1:0] samp_wait_ns, samp_wait_r;
  always @(posedge clk) samp_wait_r <= #TCQ samp_wait_ns;

  reg pd_out_r;
  always @(posedge clk) pd_out_r <= #TCQ pd_out;
  wire pd_out_sel = POC_USE_METASTABLE_SAMP == "TRUE" ? pd_out_r : pd_out;

  output psincdec;
  assign psincdec = 1'b1;
  output psen;
  reg psen_int;
  assign psen = psen_int;
 
  reg [TAPCNTRWIDTH-1:0] run_r;
   reg [TAPCNTRWIDTH-1:0] run_ns;
  always @(posedge clk) run_r <= #TCQ run_ns;
  output [TAPCNTRWIDTH-1:0] run;
  assign run = run_r;

  output run_end;
  reg run_end_int;
  assign run_end = run_end_int;

  output run_too_small;
  reg run_too_small_r, run_too_small_ns;
  always @(*) run_too_small_ns = run_end && (run <  TAPSPERKCLK/4);
  always @(posedge clk) run_too_small_r <= #TCQ run_too_small_ns;
  assign run_too_small = run_too_small_r;
  
  reg run_polarity_r;
  reg run_polarity_ns;
  always @(posedge clk) run_polarity_r <= #TCQ run_polarity_ns;
  output run_polarity;
  assign run_polarity = run_polarity_r;

  reg [SAMPCNTRWIDTH-1:0] samp_cntr_r;
  reg [SAMPCNTRWIDTH-1:0] samp_cntr_ns;
  always @(posedge clk) samp_cntr_r <= #TCQ samp_cntr_ns;
  output [SAMPCNTRWIDTH-1:0] samp_cntr;
  assign samp_cntr = samp_cntr_r;

  reg [SAMPCNTRWIDTH:0] samps_hi_r;
  reg [SAMPCNTRWIDTH:0] samps_hi_ns;
  always @(posedge clk) samps_hi_r <= #TCQ samps_hi_ns;
  output [SAMPCNTRWIDTH:0] samps_hi;
  assign samps_hi = samps_hi_r;

  reg [SAMPCNTRWIDTH:0] samps_hi_held_r;
  reg [SAMPCNTRWIDTH:0] samps_hi_held_ns;
  always @(posedge clk) samps_hi_held_r <= #TCQ samps_hi_held_ns;
  output [SAMPCNTRWIDTH:0] samps_hi_held;
  assign samps_hi_held = samps_hi_held_r;

  reg [TAPCNTRWIDTH-1:0] tap_ns, tap_r;
  always @(posedge clk) tap_r <= #TCQ tap_ns;
  output [TAPCNTRWIDTH-1:0] tap;
  assign tap = tap_r;
  
  reg [SMWIDTH-1:0] sm_ns;
  reg [SMWIDTH-1:0] sm_r;
  always @(posedge clk) sm_r <= #TCQ sm_ns;
  output [SMWIDTH-1:0] sm;
  assign sm = sm_r;

  reg samps_zero_ns, samps_zero_r, samps_one_ns, samps_one_r;
  always @(posedge clk) samps_zero_r <= #TCQ samps_zero_ns;
  always @(posedge clk) samps_one_r <= #TCQ samps_one_ns;
  output samps_zero, samps_one;
  assign samps_zero = samps_zero_r;
  assign samps_one = samps_one_r;

  wire [SAMPCNTRWIDTH:0] samps_lo = samples + ONE[SAMPCNTRWIDTH:0] - samps_hi_r;
  always @(*) begin
    samps_zero_ns = samps_zero_r;
    samps_one_ns = samps_one_r;
    samps_zero_ns = samps_lo >= samps_solid_thresh;
    samps_one_ns = samps_hi_r >= samps_solid_thresh;
  end wire new_polarity = run_polarity_ns ^ run_polarity_r;

  input poc_sample_pd;

  always @(*) begin
    
    if (rst == 1'b1) begin
      
 psen_int = 1'b0;
      sm_ns = 2'd0;
      run_polarity_ns = 1'b0;
      run_ns = {TAPCNTRWIDTH{1'b0}};
      run_end_int = 1'b0;
      samp_cntr_ns = {SAMPCNTRWIDTH{1'b0}};
      samps_hi_ns = {SAMPCNTRWIDTH+1{1'b0}};
      tap_ns = {TAPCNTRWIDTH{1'b0}};
      samp_wait_ns = MMCM_SAMP_WAIT[SAMP_WAIT_WIDTH-1:0];
      samps_hi_held_ns = {SAMPCNTRWIDTH+1{1'b0}};
    end else begin

 psen_int = 1'b0;
      sm_ns = sm_r;
      run_polarity_ns = run_polarity_r;
      run_ns = run_r;
      run_end_int = 1'b0;
      samp_cntr_ns = samp_cntr_r;
      samps_hi_ns = samps_hi_r;
      tap_ns = tap_r;
      samp_wait_ns = samp_wait_r;
      if (|samp_wait_r) samp_wait_ns = samp_wait_r - ONE[SAMP_WAIT_WIDTH-1:0];
      samps_hi_held_ns = samps_hi_held_r;

case (sm_r)
        2'd0: begin
	  if (~|samp_wait_r && poc_sample_pd | POC_USE_METASTABLE_SAMP == "TRUE") begin
	    if (POC_USE_METASTABLE_SAMP == "TRUE") samp_wait_ns = ONE[SAMP_WAIT_WIDTH-1:0];
	    if ({1'b0, samp_cntr_r} == samples) sm_ns = 2'd1;
	    samps_hi_ns = samps_hi_r + {{SAMPCNTRWIDTH{1'b0}}, pd_out_sel};
	    samp_cntr_ns = samp_cntr_r + ONE[SAMPCNTRWIDTH-1:0];
	  end
        end
	
	2'd1:begin
	   sm_ns = 2'd2;
        end

        2'd2:begin
	  sm_ns = 2'd3;
	  psen_int = 1'b1;
	  samp_cntr_ns = {SAMPCNTRWIDTH{1'b0}};
	  samps_hi_ns = {SAMPCNTRWIDTH+1{1'b0}};
	  samps_hi_held_ns = samps_hi_r;
	  tap_ns = (tap_r < TAPSPERKCLK[TAPCNTRWIDTH-1:0] - ONE[TAPCNTRWIDTH-1:0])
	             ? tap_r + ONE[TAPCNTRWIDTH-1:0]
		     : {TAPCNTRWIDTH{1'b0}};

	  if (run_polarity_r) begin
	    if (samps_zero_r) run_polarity_ns = 1'b0;
	  end else begin
	    if (samps_one_r) run_polarity_ns = 1'b1;
	  end
	  if (new_polarity) begin
            run_ns ={TAPCNTRWIDTH{1'b0}};
	    run_end_int = 1'b1;
	  end else run_ns = run_r + ONE[TAPCNTRWIDTH-1:0];
        end

        2'd3:begin
	  samp_wait_ns = MMCM_SAMP_WAIT[SAMP_WAIT_WIDTH-1:0] - ONE[SAMP_WAIT_WIDTH-1:0];
	  if (psdone) sm_ns = 2'd0;
        end
	
      endcase end end endmodule 