// SVA checker for alt_mem_ddrx_mm_st_converter
// Bindable, protocol-accurate, with shadow model to verify outputs and control

module alt_mem_ddrx_mm_st_converter_sva #(
  parameter AVL_SIZE_WIDTH     = 3,
  parameter AVL_ADDR_WIDTH     = 25,
  parameter AVL_DATA_WIDTH     = 32,
  parameter LOCAL_ID_WIDTH     = 8,
  parameter CFG_DWIDTH_RATIO   = 4,
  parameter CFG_MM_ST_CONV_REG = 0
)(
  input                       ctl_clk,
  input                       ctl_reset_n,
  input                       ctl_half_clk,
  input                       ctl_half_clk_reset_n,

  output                      avl_ready,
  input                       avl_read_req,
  input                       avl_write_req,
  input  [AVL_SIZE_WIDTH-1:0] avl_size,
  input                       avl_burstbegin,
  input  [AVL_ADDR_WIDTH-1:0] avl_addr,
  output                      avl_rdata_valid,
  output [3:0]                local_rdata_error,
  output [AVL_DATA_WIDTH-1:0] avl_rdata,
  input  [AVL_DATA_WIDTH-1:0] avl_wdata,
  input  [AVL_DATA_WIDTH/8-1:0]   avl_be,

  input                       local_multicast,
  input                       local_autopch_req,
  input                       local_priority,

  input                       itf_cmd_ready,
  output                      itf_cmd_valid,
  output                      itf_cmd,
  output [AVL_ADDR_WIDTH-1:0] itf_cmd_address,
  output [AVL_SIZE_WIDTH-1:0] itf_cmd_burstlen,
  output [LOCAL_ID_WIDTH-1:0] itf_cmd_id,
  output                      itf_cmd_priority,
  output                      itf_cmd_autopercharge,
  output                      itf_cmd_multicast,

  input                       itf_wr_data_ready,
  output                      itf_wr_data_valid,
  output [AVL_DATA_WIDTH-1:0] itf_wr_data,
  output [AVL_DATA_WIDTH/8-1:0]   itf_wr_data_byte_en,
  output                      itf_wr_data_begin,
  output                      itf_wr_data_last,
  output [LOCAL_ID_WIDTH-1:0] itf_wr_data_id,

  output                     itf_rd_data_ready,
  input                      itf_rd_data_valid,
  input [AVL_DATA_WIDTH-1:0] itf_rd_data,
  input                      itf_rd_data_error,
  input                      itf_rd_data_begin,
  input                      itf_rd_data_last,
  input [LOCAL_ID_WIDTH-1:0] itf_rd_data_id
);

  localparam AVL_BE_WIDTH = AVL_DATA_WIDTH/8;

  default clocking cb @(posedge ctl_clk); endclocking
  default disable iff (!ctl_reset_n)

  // Shadow model of registered inputs and internal state
  logic                       avl_read_req_reg_s;
  logic                       avl_write_req_reg_s;
  logic [AVL_SIZE_WIDTH-1:0]  avl_size_reg_s;
  logic [AVL_ADDR_WIDTH-1:0]  avl_addr_reg_s;
  logic [AVL_DATA_WIDTH-1:0]  avl_wdata_reg_s;
  logic [AVL_BE_WIDTH-1:0]    avl_be_reg_s;

  logic                       local_multicast_reg_s;
  logic                       local_autopch_req_reg_s;
  logic                       local_priority_reg_s;

  logic                       itf_rd_data_valid_reg_s;
  logic [AVL_DATA_WIDTH-1:0]  itf_rd_data_reg_s;
  logic [3:0]                 itf_rd_data_error_reg_s;

  logic [AVL_SIZE_WIDTH-1:0]  burst_counter_s;
  logic                       data_pass_s;

  // Derived combinational mirrors
  logic                       itf_cmd_s;
  logic                       itf_wr_if_ready_s;
  logic                       itf_cmd_valid_s;
  logic                       itf_wr_data_valid_s;
  logic                       int_ready_s;
  logic [3:0]                 local_rdata_error_s;

  // Build mirrors
  // int_ready depends on data_pass and write/read mode
  always_comb begin
    itf_cmd_s          = avl_write_req_reg_s;
    itf_wr_if_ready_s  = itf_wr_data_ready & avl_write_req_reg_s & ~data_pass_s;
    itf_cmd_valid_s    = avl_read_req_reg_s | itf_wr_if_ready_s;
    itf_wr_data_valid_s= data_pass_s ? avl_write_req_reg_s : (itf_cmd_ready & avl_write_req_reg_s);
    int_ready_s        = data_pass_s ? itf_wr_data_ready
                                     : (itf_cmd_s ? (itf_wr_data_ready & itf_cmd_ready) : itf_cmd_ready);
    if (CFG_MM_ST_CONV_REG==0) begin
      local_rdata_error_s = {4{itf_rd_data_error}};
    end else begin
      local_rdata_error_s = {3'b000, itf_rd_data_error};
    end
  end

  // Registered inputs shadow
  generate
    if (CFG_MM_ST_CONV_REG==0) begin : g_unreg
      always_comb begin
        avl_read_req_reg_s     = avl_read_req;
        avl_write_req_reg_s    = avl_write_req;
        avl_size_reg_s         = avl_size;
        avl_addr_reg_s         = avl_addr;
        avl_wdata_reg_s        = avl_wdata;
        avl_be_reg_s           = avl_be;
        local_multicast_reg_s  = local_multicast;
        local_autopch_req_reg_s= local_autopch_req;
        local_priority_reg_s   = local_priority;

        itf_rd_data_valid_reg_s= itf_rd_data_valid;
        itf_rd_data_reg_s      = itf_rd_data;
        itf_rd_data_error_reg_s= local_rdata_error_s;
      end
    end else begin : g_reg
      always_ff @(posedge ctl_clk or negedge ctl_reset_n) begin
        if (!ctl_reset_n) begin
          avl_read_req_reg_s      <= 1'b0;
          avl_write_req_reg_s     <= 1'b0;
          avl_size_reg_s          <= '0;
          avl_addr_reg_s          <= '0;
          avl_wdata_reg_s         <= '0;
          avl_be_reg_s            <= '0;
          local_multicast_reg_s   <= 1'b0;
          local_autopch_req_reg_s <= 1'b0;
          local_priority_reg_s    <= 1'b0;

          itf_rd_data_valid_reg_s <= 1'b0;
          itf_rd_data_reg_s       <= '0;
          itf_rd_data_error_reg_s <= 4'b0;
        end else begin
          if (int_ready_s) begin
            avl_read_req_reg_s      <= avl_read_req;
            avl_write_req_reg_s     <= avl_write_req;
            avl_size_reg_s          <= avl_size;
            avl_addr_reg_s          <= avl_addr;
            avl_wdata_reg_s         <= avl_wdata;
            avl_be_reg_s            <= avl_be;
            local_multicast_reg_s   <= local_multicast;
            local_autopch_req_reg_s <= local_autopch_req;
            local_priority_reg_s    <= local_priority;
          end
          itf_rd_data_valid_reg_s <= itf_rd_data_valid;
          itf_rd_data_reg_s       <= itf_rd_data;
          itf_rd_data_error_reg_s <= {3'b000, itf_rd_data_error};
        end
      end
    end
  endgenerate

  // Burst/data_pass mirrors
  always_ff @(posedge ctl_clk or negedge ctl_reset_n) begin
    if (!ctl_reset_n) begin
      burst_counter_s <= '0;
    end else begin
      if (itf_wr_if_ready_s && (avl_size_reg_s > {{(AVL_SIZE_WIDTH-1){1'b0}},1'b1}) && itf_cmd_ready)
        burst_counter_s <= avl_size_reg_s - {{(AVL_SIZE_WIDTH-1){1'b0}},1'b1};
      else if (avl_write_req_reg_s && itf_wr_data_ready)
        burst_counter_s <= burst_counter_s - {{(AVL_SIZE_WIDTH-1){1'b0}},1'b1};
    end
  end

  always_ff @(posedge ctl_clk or negedge ctl_reset_n) begin
    if (!ctl_reset_n) begin
      data_pass_s <= 1'b0;
    end else begin
      if (itf_wr_if_ready_s && (avl_size_reg_s > {{(AVL_SIZE_WIDTH-1){1'b0}},1'b1}) && itf_cmd_ready)
        data_pass_s <= 1'b1;
      else if ((burst_counter_s == {{(AVL_SIZE_WIDTH-1){1'b0}},1'b1}) && avl_write_req_reg_s && itf_wr_data_ready)
        data_pass_s <= 1'b0;
    end
  end

  // Core equivalence assertions (outputs equal spec)
  assert property (avl_ready == int_ready_s);
  assert property (itf_cmd_valid == itf_cmd_valid_s);
  assert property (itf_cmd == avl_write_req_reg_s);

  assert property (itf_cmd_address   == avl_addr_reg_s);
  assert property (itf_cmd_burstlen  == avl_size_reg_s);
  assert property (itf_cmd_priority  == local_priority_reg_s);
  assert property (itf_cmd_autopercharge == local_autopch_req_reg_s);
  assert property (itf_cmd_multicast == local_multicast_reg_s);

  assert property (itf_wr_data_valid == itf_wr_data_valid_s);
  assert property (itf_wr_data       == avl_wdata_reg_s);
  assert property (itf_wr_data_byte_en == avl_be_reg_s);

  assert property (itf_rd_data_ready == 1'b1);
  assert property (avl_rdata_valid == itf_rd_data_valid_reg_s);
  assert property (avl_rdata == itf_rd_data_reg_s);
  assert property (local_rdata_error == itf_rd_data_error_reg_s);

  // Constants
  assert property (itf_cmd_id == {LOCAL_ID_WIDTH{1'b0}});
  assert property (itf_wr_data_begin == 1'b0);
  assert property (itf_wr_data_last  == 1'b0);
  assert property (itf_wr_data_id == {LOCAL_ID_WIDTH{1'b0}});

  // Protocol/gating assertions
  // itf_cmd_valid only when read_req_reg or starting write
  assert property (itf_cmd_valid |-> (avl_read_req_reg_s || (itf_wr_data_ready && avl_write_req_reg_s && !data_pass_s)));

  // Write data valid implies write request present
  assert property (itf_wr_data_valid |-> avl_write_req_reg_s);

  // Non-data_pass write must wait for cmd_ready
  assert property ((!data_pass_s && avl_write_req_reg_s && !itf_cmd_ready) |-> (!itf_wr_data_valid && !avl_ready));

  // During data_pass, ready tracks wr_data_ready
  assert property (data_pass_s |-> (avl_ready == itf_wr_data_ready));

  // data_pass and burst_counter evolution
  assert property ((itf_wr_if_ready_s && itf_cmd_ready && (avl_size_reg_s > {{(AVL_SIZE_WIDTH-1){1'b0}},1'b1})) |=> (data_pass_s && (burst_counter_s == $past(avl_size_reg_s)-{{(AVL_SIZE_WIDTH-1){1'b0}},1'b1})));

  assert property (data_pass_s |-> (burst_counter_s > '0));

  assert property ((data_pass_s && avl_write_req_reg_s && itf_wr_data_ready) |=> burst_counter_s == $past(burst_counter_s) - {{(AVL_SIZE_WIDTH-1){1'b0}},1'b1});

  assert property ((itf_wr_if_ready_s && itf_cmd_ready && (avl_size_reg_s <= {{(AVL_SIZE_WIDTH-1){1'b0}},1'b1})) |=> !data_pass_s);

  // When registered mode, outputs driven by registered inputs must be stable while avl_ready=0
  generate if (CFG_MM_ST_CONV_REG!=0) begin
    assert property (!avl_ready |=> ($stable(itf_cmd_address) && $stable(itf_cmd_burstlen) &&
                                     $stable(itf_cmd_priority) && $stable(itf_cmd_autopercharge) &&
                                     $stable(itf_cmd_multicast) && $stable(itf_wr_data) &&
                                     $stable(itf_wr_data_byte_en)));
  end endgenerate

  // Read command encoding: read => itf_cmd==0 when cmd_valid asserted from read
  assert property (avl_read_req_reg_s && !avl_write_req_reg_s |-> (itf_cmd_valid && (itf_cmd==1'b0)));

  // Coverage

  // Read command accepted
  cover property (avl_read_req_reg_s && !avl_write_req_reg_s ##1 itf_cmd_ready && itf_cmd_valid && (itf_cmd==1'b0) && avl_ready);

  // Single-beat write (size<=1)
  cover property ((avl_write_req_reg_s && (avl_size_reg_s <= {{(AVL_SIZE_WIDTH-1){1'b0}},1'b1}) && itf_cmd_ready && itf_wr_data_ready && !data_pass_s)
                   ##1 itf_wr_data_valid && avl_ready && !data_pass_s);

  // Multi-beat write start and completion (size>1)
  cover property ((avl_write_req_reg_s && (avl_size_reg_s > {{(AVL_SIZE_WIDTH-1){1'b0}},1'b1}) && itf_cmd_ready && itf_wr_data_ready && !data_pass_s)
                   ##1 data_pass_s ##[1:$] (avl_write_req_reg_s && itf_wr_data_ready && (burst_counter_s=={{(AVL_SIZE_WIDTH-1){1'b0}},1'b1}))
                   ##1 !data_pass_s);

  // Backpressure on cmd_ready before first beat
  cover property (avl_write_req_reg_s && !data_pass_s && !itf_cmd_ready ##1 itf_cmd_ready && itf_wr_data_ready && itf_cmd_valid);

  // Backpressure mid-burst on wr_data_ready
  cover property ((data_pass_s && !itf_wr_data_ready) ##1 (data_pass_s && itf_wr_data_ready));

endmodule

// Bind into DUT
bind alt_mem_ddrx_mm_st_converter
  alt_mem_ddrx_mm_st_converter_sva #(
    .AVL_SIZE_WIDTH(AVL_SIZE_WIDTH),
    .AVL_ADDR_WIDTH(AVL_ADDR_WIDTH),
    .AVL_DATA_WIDTH(AVL_DATA_WIDTH),
    .LOCAL_ID_WIDTH(LOCAL_ID_WIDTH),
    .CFG_DWIDTH_RATIO(CFG_DWIDTH_RATIO),
    .CFG_MM_ST_CONV_REG(CFG_MM_ST_CONV_REG)
  ) i_alt_mem_ddrx_mm_st_converter_sva (.*);