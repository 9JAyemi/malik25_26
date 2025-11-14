// SVA for hapara_axis_id_generator_v1_0_S00_AXI
// Bind once in your TB:
// bind hapara_axis_id_generator_v1_0_S00_AXI hapara_axis_id_generator_v1_0_S00_AXI_sva #(.C_S_AXI_DATA_WIDTH(C_S_AXI_DATA_WIDTH), .C_S_AXI_ADDR_WIDTH(C_S_AXI_ADDR_WIDTH)) sva_i (.*);

module hapara_axis_id_generator_v1_0_S00_AXI_sva #(
  parameter int C_S_AXI_DATA_WIDTH = 32,
  parameter int C_S_AXI_ADDR_WIDTH = 4
) (
  input  logic                               S_AXI_ACLK,
  input  logic                               S_AXI_ARESETN,
  input  logic [C_S_AXI_ADDR_WIDTH-1:0]      S_AXI_AWADDR,
  input  logic [2:0]                         S_AXI_AWPROT,
  input  logic                               S_AXI_AWVALID,
  input  logic                               S_AXI_WVALID,
  input  logic [(C_S_AXI_DATA_WIDTH/8)-1:0]  S_AXI_WSTRB,
  input  logic [C_S_AXI_DATA_WIDTH-1:0]      S_AXI_WDATA,
  input  logic                               S_AXI_BREADY,
  input  logic [C_S_AXI_ADDR_WIDTH-1:0]      S_AXI_ARADDR,
  input  logic [2:0]                         S_AXI_ARPROT,
  input  logic                               S_AXI_ARVALID,
  input  logic                               S_AXI_RREADY,
  input  logic                               Finish,
  input  logic                               En,
  input  logic [C_S_AXI_DATA_WIDTH-1:0]      org,
  input  logic [C_S_AXI_DATA_WIDTH-1:0]      len,
  input  logic [C_S_AXI_DATA_WIDTH-1:0]      numOfSlv,

  // DUT internals (bound by name)
  input  logic                               axi_awready,
  input  logic                               axi_wready,
  input  logic [1:0]                         axi_bresp,
  input  logic                               axi_bvalid,
  input  logic [C_S_AXI_ADDR_WIDTH-1:0]      axi_araddr,
  input  logic                               axi_arready,
  input  logic [C_S_AXI_DATA_WIDTH-1:0]      axi_rdata,
  input  logic [1:0]                         axi_rresp,
  input  logic                               axi_rvalid,

  input  logic [C_S_AXI_ADDR_WIDTH-1:0]      axi_awaddr,
  input  logic                               slv_reg_wren,
  input  logic                               slv_reg_rden,
  input  logic [C_S_AXI_DATA_WIDTH-1:0]      slv_reg0,
  input  logic [C_S_AXI_DATA_WIDTH-1:0]      slv_reg1,
  input  logic [C_S_AXI_DATA_WIDTH-1:0]      slv_reg2,
  input  logic [C_S_AXI_DATA_WIDTH-1:0]      slv_reg3,
  input  logic [C_S_AXI_DATA_WIDTH-1:0]      reg_data_out,

  input  logic [C_S_AXI_DATA_WIDTH-1:0]      reg_org,
  input  logic [C_S_AXI_DATA_WIDTH-1:0]      reg_len,
  input  logic [C_S_AXI_DATA_WIDTH-1:0]      reg_numOfSlv,

  input  logic [2:0]                         curr_state,
  input  logic [2:0]                         next_state,
  input  logic                               data_ready
);

  localparam int ADDR_LSB            = (C_S_AXI_DATA_WIDTH/32) + 1;
  localparam int OPT_MEM_ADDR_BITS   = 1;
  localparam int LENGTH              = C_S_AXI_DATA_WIDTH/2;

  localparam logic [2:0] S_RESET     = 3'b001;
  localparam logic [2:0] S_COUNTING  = 3'b010;
  localparam logic [2:0] S_FINISH    = 3'b100;

  wire [1:0] aw_sel = axi_awaddr[ADDR_LSB+OPT_MEM_ADDR_BITS : ADDR_LSB];
  wire [1:0] ar_sel = axi_araddr[ADDR_LSB+OPT_MEM_ADDR_BITS : ADDR_LSB];

  default clocking cb @(posedge S_AXI_ACLK); endclocking
  default disable iff (!S_AXI_ARESETN)

  // Reset invariants (active-low)
  assert property (@cb !S_AXI_ARESETN |-> !axi_awready && !axi_wready && !axi_bvalid && !axi_arready && !axi_rvalid
                                 && (slv_reg0==0) && (slv_reg1==0) && (slv_reg2==0) && (slv_reg3==0)
                                 && (reg_org==0) && (reg_len==0) && (reg_numOfSlv==0));

  // AW/W ready behavior
  assert property (@cb axi_awready == axi_wready);
  assert property (@cb axi_awready |-> (S_AXI_AWVALID && S_AXI_WVALID));
  assert property (@cb axi_wready  |-> (S_AXI_WVALID  && S_AXI_AWVALID));
  assert property (@cb axi_awready |-> ##1 !axi_awready);
  assert property (@cb axi_wready  |-> ##1 !axi_wready);
  assert property (@cb axi_awready |-> axi_awaddr == $past(S_AXI_AWADDR));

  // Write response
  assert property (@cb (axi_awready && axi_wready) |=> axi_bvalid);
  assert property (@cb axi_bvalid && !S_AXI_BREADY |=> axi_bvalid);
  assert property (@cb axi_bvalid |-> (axi_bresp == 2'b00));

  // AR/R behavior
  assert property (@cb axi_arready |-> S_AXI_ARVALID);
  assert property (@cb axi_arready |-> ##1 !axi_arready);
  assert property (@cb (axi_arready && S_AXI_ARVALID) |=> axi_rvalid);
  assert property (@cb (axi_arready && S_AXI_ARVALID) |=> axi_araddr == $past(S_AXI_ARADDR));
  assert property (@cb axi_rvalid && !S_AXI_RREADY |=> axi_rvalid);
  assert property (@cb axi_rvalid |-> (axi_rresp == 2'b00));
  assert property (@cb axi_rvalid && !S_AXI_RREADY |=> $stable(axi_rdata));
  assert property (@cb slv_reg_rden |=> axi_rdata == $past(reg_data_out));

  // Read data mux correctness
  assert property (@cb (ar_sel==2'h0) |-> (reg_data_out==slv_reg0));
  assert property (@cb (ar_sel==2'h1) |-> (reg_data_out==slv_reg1));
  assert property (@cb (ar_sel==2'h2) |-> (reg_data_out==slv_reg2));
  assert property (@cb (ar_sel==2'h3) |-> (reg_data_out==slv_reg3));

  // WSTRB write semantics (byte enables) for slv_reg0..2
  genvar b;
  generate
    for (b=0; b<(C_S_AXI_DATA_WIDTH/8); b++) begin : gen_wstrb_chk
      // reg0
      assert property (@cb slv_reg_wren && (aw_sel==2'h0) && (S_AXI_WSTRB[b]==1'b0)
                       |=> slv_reg0[b*8 +: 8] == $past(slv_reg0[b*8 +: 8]));
      assert property (@cb slv_reg_wren && (aw_sel==2'h0) && (S_AXI_WSTRB[b]==1'b1)
                       |=> slv_reg0[b*8 +: 8] == $past(S_AXI_WDATA[b*8 +: 8]));
      // reg1
      assert property (@cb slv_reg_wren && (aw_sel==2'h1) && (S_AXI_WSTRB[b]==1'b0)
                       |=> slv_reg1[b*8 +: 8] == $past(slv_reg1[b*8 +: 8]));
      assert property (@cb slv_reg_wren && (aw_sel==2'h1) && (S_AXI_WSTRB[b]==1'b1)
                       |=> slv_reg1[b*8 +: 8] == $past(S_AXI_WDATA[b*8 +: 8]));
      // reg2
      assert property (@cb slv_reg_wren && (aw_sel==2'h2) && (S_AXI_WSTRB[b]==1'b0)
                       |=> slv_reg2[b*8 +: 8] == $past(slv_reg2[b*8 +: 8]));
      assert property (@cb slv_reg_wren && (aw_sel==2'h2) && (S_AXI_WSTRB[b]==1'b1)
                       |=> slv_reg2[b*8 +: 8] == $past(S_AXI_WDATA[b*8 +: 8]));
    end
  endgenerate

  // No write to slv_reg0..2 on invalid address
  assert property (@cb slv_reg_wren && (aw_sel==2'h3)
                   |=> (slv_reg0==$past(slv_reg0)) && (slv_reg1==$past(slv_reg1)) && (slv_reg2==$past(slv_reg2)));

  // slv_reg0..2 cleared in counting; slv_reg3 reflects state
  assert property (@cb (curr_state==S_COUNTING) |-> (slv_reg0==0) && (slv_reg1==0) && (slv_reg2==0));
  assert property (@cb (curr_state==S_RESET) || (curr_state==S_COUNTING) |-> (slv_reg3==0));
  assert property (@cb (curr_state==S_FINISH) |-> (slv_reg3==1));

  // Register sampling/holding
  assert property (@cb (curr_state==S_RESET)
                   |=> (reg_org==$past(slv_reg0)) && (reg_len==$past(slv_reg1)) && (reg_numOfSlv==$past(slv_reg2)));
  assert property (@cb (curr_state!=S_RESET)
                   |=> (reg_org==$past(reg_org)) && (reg_len==$past(reg_len)) && (reg_numOfSlv==$past(reg_numOfSlv)));

  // Outputs mirror internal regs
  assert property (@cb org==reg_org && len==reg_len && numOfSlv==reg_numOfSlv);

  // En definition
  assert property (@cb En == (curr_state==S_COUNTING));

  // data_ready definition
  assert property (@cb data_ready == ((slv_reg1[C_S_AXI_DATA_WIDTH-1:LENGTH] != {LENGTH{1'b0}})
                                   &&  (slv_reg1[LENGTH-1:0]                != {LENGTH{1'b0}})));

  // FSM: legal states only
  assert property (@cb curr_state inside {S_RESET,S_COUNTING,S_FINISH});

  // FSM transitions
  assert property (@cb $past(curr_state)==S_RESET    &&  $past(data_ready) |-> curr_state==S_COUNTING);
  assert property (@cb $past(curr_state)==S_RESET    && !$past(data_ready) |-> curr_state==S_RESET);
  assert property (@cb $past(curr_state)==S_COUNTING &&  $past(Finish)     |-> curr_state==S_FINISH);
  assert property (@cb $past(curr_state)==S_COUNTING && !$past(Finish)     |-> curr_state==S_COUNTING);
  assert property (@cb $past(curr_state)==S_FINISH   &&  $past(data_ready) |-> curr_state==S_RESET);
  assert property (@cb $past(curr_state)==S_FINISH   && !$past(data_ready) |-> curr_state==S_FINISH);

  // Coverage

  // Full state traversal
  cover property (@cb curr_state==S_RESET ##1 curr_state==S_COUNTING ##1 curr_state==S_FINISH ##1 curr_state==S_RESET);

  // Write handshakes to each address
  cover property (@cb (axi_awready && axi_wready && aw_sel==2'h0));
  cover property (@cb (axi_awready && axi_wready && aw_sel==2'h1));
  cover property (@cb (axi_awready && axi_wready && aw_sel==2'h2));
  cover property (@cb (axi_awready && axi_wready && aw_sel==2'h3));

  // Read handshakes to each address
  cover property (@cb (axi_arready && S_AXI_ARVALID && ar_sel==2'h0));
  cover property (@cb (axi_arready && S_AXI_ARVALID && ar_sel==2'h1));
  cover property (@cb (axi_arready && S_AXI_ARVALID && ar_sel==2'h2));
  cover property (@cb (axi_arready && S_AXI_ARVALID && ar_sel==2'h3));

  // Partial byte write occurrence
  cover property (@cb (axi_awready && axi_wready && (S_AXI_WSTRB != {C_S_AXI_DATA_WIDTH/8{1'b1}})));

  // data_ready and Finish driven transitions
  cover property (@cb (curr_state==S_RESET && data_ready) ##1 (curr_state==S_COUNTING));
  cover property (@cb (curr_state==S_COUNTING && Finish)  ##1 (curr_state==S_FINISH));

endmodule