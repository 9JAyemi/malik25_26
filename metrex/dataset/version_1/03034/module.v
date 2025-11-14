

module mig_7series_v2_3_ddr_phy_ocd_mux #
  (parameter DQS_CNT_WIDTH   = 3,
   parameter DQS_WIDTH       = 8,
   parameter TCQ             = 100)
  (
  ktap_at_left_edge, ktap_at_right_edge, mmcm_edge_detect_rdy,
  po_stg3_incdec, po_en_stg3, po_en_stg23, po_stg23_sel,
  po_stg23_incdec, po_rdy, wl_po_fine_cnt_sel, oclk_prech_req,
  clk, rst, ocd_ktap_right, ocd_ktap_left, lim2poc_ktap_right,
  lim2poc_rdy, ocd_edge_detect_rdy, lim2stg2_inc, lim2stg2_dec,
  lim2stg3_inc, lim2stg3_dec, ocd2stg2_inc, ocd2stg2_dec,
  ocd_cntlr2stg2_dec, ocd2stg3_inc, ocd2stg3_dec, wl_po_fine_cnt,
  oclkdelay_calib_cnt, lim2init_prech_req, ocd_prech_req
  );

  function integer clogb2 (input integer size); begin
      size = size - 1;
      for (clogb2=1; size>1; clogb2=clogb2+1)
            size = size >> 1;
    end
  endfunction localparam PO_WAIT = 15;
  localparam POW_WIDTH = clogb2(PO_WAIT);
  localparam ONE = 1;
  localparam TWO = 2;

  input clk;
  input rst;

  input ocd_ktap_right, ocd_ktap_left;
  input lim2poc_ktap_right;
  output ktap_at_left_edge, ktap_at_right_edge;
  assign ktap_at_left_edge = ocd_ktap_left;
  assign ktap_at_right_edge = lim2poc_ktap_right || ocd_ktap_right;
  
  input lim2poc_rdy;
  input ocd_edge_detect_rdy;
  output mmcm_edge_detect_rdy;
  assign mmcm_edge_detect_rdy = lim2poc_rdy || ocd_edge_detect_rdy;
  
  output po_stg3_incdec;
  output po_en_stg3;
  assign po_stg3_incdec = 1'b0;
  assign po_en_stg3 = 1'b0;


  reg [1:0] po_setup_ns, po_setup_r;
  always @(posedge clk) po_setup_r <= #TCQ po_setup_ns;

  input lim2stg2_inc;
  input lim2stg2_dec;

  input lim2stg3_inc;
  input lim2stg3_dec;

  input ocd2stg2_inc;
  input ocd2stg2_dec;
  input ocd_cntlr2stg2_dec;
  
  input ocd2stg3_inc;
  input ocd2stg3_dec;

  wire setup_po = 
       lim2stg2_inc || lim2stg2_dec || lim2stg3_inc || lim2stg3_dec ||
       ocd2stg2_inc || ocd2stg2_dec || ocd2stg3_inc || ocd2stg3_dec || ocd_cntlr2stg2_dec;

  always @(*) begin
    po_setup_ns = po_setup_r;
    if (rst) po_setup_ns = 2'b00;
    else if (setup_po) po_setup_ns = 2'b11;
    else if (|po_setup_r) po_setup_ns = po_setup_r - 2'b01;
  end

  reg po_en_stg23_r;
  wire po_en_stg23_ns = ~rst && po_setup_r == 2'b01;
  always @(posedge clk) po_en_stg23_r <= #TCQ po_en_stg23_ns;
  output po_en_stg23;
  assign po_en_stg23 = po_en_stg23_r; 

  wire sel_stg3 = lim2stg3_inc || lim2stg3_dec || ocd2stg3_inc || ocd2stg3_dec;

  reg [POW_WIDTH-1:0] po_wait_r, po_wait_ns;
  reg po_stg23_sel_r;
  wire po_stg23_sel_ns = ~rst && (setup_po 
                                    ? sel_stg3
                                       ? 1'b1 
                                       : 1'b0 
                                    : po_stg23_sel_r && !(po_wait_r == ONE[POW_WIDTH-1:0]));
  always @(posedge clk) po_stg23_sel_r <= #TCQ po_stg23_sel_ns;
  output po_stg23_sel;
  assign po_stg23_sel = po_stg23_sel_r;

  wire po_inc = lim2stg2_inc || lim2stg3_inc || ocd2stg2_inc || ocd2stg3_inc;

  reg po_stg23_incdec_r;
  wire po_stg23_incdec_ns = ~rst && (setup_po ? po_inc ? 1'b1 : 1'b0 : po_stg23_incdec_r);
  always @(posedge clk) po_stg23_incdec_r <= #TCQ po_stg23_incdec_ns;
  output po_stg23_incdec;
  assign po_stg23_incdec = po_stg23_incdec_r;


  always @(posedge clk) po_wait_r <= #TCQ po_wait_ns;
  always @(*) begin
    po_wait_ns = po_wait_r;
    if (rst) po_wait_ns = {POW_WIDTH{1'b0}};
    else if (po_en_stg23_r) po_wait_ns = PO_WAIT[POW_WIDTH-1:0] - ONE[POW_WIDTH-1:0];
    else if (po_wait_r != {POW_WIDTH{1'b0}}) po_wait_ns = po_wait_r - ONE[POW_WIDTH-1:0];	   
  end
  
  wire po_rdy_ns = ~(setup_po || |po_setup_r || |po_wait_ns);
  reg po_rdy_r;
  always @(posedge clk) po_rdy_r <= #TCQ po_rdy_ns;
  
  output po_rdy;
  assign po_rdy = po_rdy_r;

  input [6*DQS_WIDTH-1:0] wl_po_fine_cnt;
  input [DQS_CNT_WIDTH:0] oclkdelay_calib_cnt;
  wire [6*DQS_WIDTH-1:0] wl_po_fine_shifted = wl_po_fine_cnt >> oclkdelay_calib_cnt*6;
  output [5:0] wl_po_fine_cnt_sel;
  assign wl_po_fine_cnt_sel = wl_po_fine_shifted[5:0];

  input lim2init_prech_req;
  input ocd_prech_req;
  output oclk_prech_req;
  assign oclk_prech_req = ocd_prech_req || lim2init_prech_req;
	
endmodule 