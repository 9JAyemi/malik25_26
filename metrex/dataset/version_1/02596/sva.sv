// SVA for line_reader. Bind this module to the DUT.
// Focus: AXI-AR protocol, read-burst accounting, addressing, write-port, and EOL behavior.
`ifndef LINE_READER_SVA
`define LINE_READER_SVA

module line_reader_sva #(
  parameter integer C_IMG_WBITS            = 12,
  parameter integer C_WRITE_INDEX_BITS     = 10,
  parameter integer C_M_AXI_BURST_LEN      = 16,
  parameter integer C_M_AXI_ADDR_WIDTH     = 32,
  parameter integer C_M_AXI_DATA_WIDTH     = 32
)(
  input  wire [C_IMG_WBITS-1:0]                 img_width,
  input  wire                                   sol,
  input  wire [C_M_AXI_ADDR_WIDTH-1:0]          line_addr,

  input  wire                                   end_of_line_pulse,
  input  wire [C_M_AXI_DATA_WIDTH-1:0]          wr_data,
  input  wire [C_WRITE_INDEX_BITS-1:0]          wr_addr,
  input  wire                                   wr_en,

  input  wire                                   M_AXI_ACLK,
  input  wire                                   M_AXI_ARESETN,

  input  wire [C_M_AXI_ADDR_WIDTH-1:0]          M_AXI_ARADDR,
  input  wire [7:0]                             M_AXI_ARLEN,
  input  wire [2:0]                             M_AXI_ARSIZE,
  input  wire [1:0]                             M_AXI_ARBURST,
  input  wire                                   M_AXI_ARLOCK,
  input  wire [3:0]                             M_AXI_ARCACHE,
  input  wire [2:0]                             M_AXI_ARPROT,
  input  wire [3:0]                             M_AXI_ARQOS,
  input  wire                                   M_AXI_ARVALID,
  input  wire                                   M_AXI_ARREADY,

  input  wire [C_M_AXI_DATA_WIDTH-1:0]          M_AXI_RDATA,
  input  wire [1:0]                             M_AXI_RRESP,
  input  wire                                   M_AXI_RLAST,
  input  wire                                   M_AXI_RVALID,
  input  wire                                   M_AXI_RREADY
);

  localparam int unsigned BYTES        = C_M_AXI_DATA_WIDTH/8;
  localparam int unsigned SHIFT        = (C_IMG_WBITS - C_WRITE_INDEX_BITS);
  localparam int unsigned ADATA_PIXELS = (1<<SHIFT);
  localparam int unsigned BURST_BYTES  = C_M_AXI_BURST_LEN * BYTES;
  localparam int unsigned ARSIZE_EXP   = $clog2(BYTES);

  wire clk   = M_AXI_ACLK;
  wire rst_n = M_AXI_ARESETN;

  wire ar_hs = M_AXI_ARVALID && M_AXI_ARREADY;
  wire r_hs  = M_AXI_RVALID  && M_AXI_RREADY;

  // Scoreboard for bursts and line progress
  bit                  in_burst, in_line;
  int unsigned         beats_left_line, beats_left_burst;
  int unsigned         beats_per_line;
  logic [C_M_AXI_ADDR_WIDTH-1:0] expect_araddr;

  // AXI-AR stable while waiting
  assert property (@(posedge clk) disable iff (!rst_n)
    M_AXI_ARVALID && !M_AXI_ARREADY |=> M_AXI_ARVALID &&
    $stable({M_AXI_ARADDR,M_AXI_ARLEN,M_AXI_ARSIZE,M_AXI_ARBURST,
             M_AXI_ARLOCK,M_AXI_ARCACHE,M_AXI_ARPROT,M_AXI_ARQOS})
  );

  // First AR must follow SOL soon and AR eventually handshakes
  assert property (@(posedge clk) disable iff (!rst_n)
    sol |-> ##[1:3] M_AXI_ARVALID
  );
  assert property (@(posedge clk) disable iff (!rst_n)
    sol |-> ##[1:16] ar_hs
  );

  // RLAST implies RVALID
  assert property (@(posedge clk) disable iff (!rst_n)
    M_AXI_RLAST |-> M_AXI_RVALID
  );

  // Write side mirrors R channel
  assert property (@(posedge clk) disable iff (!rst_n)
    wr_en == (M_AXI_RVALID && M_AXI_RREADY)
  );
  assert property (@(posedge clk) disable iff (!rst_n)
    wr_en |-> (wr_data == M_AXI_RDATA)
  );

  // wr_addr behavior
  assert property (@(posedge clk) disable iff (!rst_n)
    sol |=> wr_addr == '0
  );
  assert property (@(posedge clk) disable iff (!rst_n)
    (r_hs && !sol) |=> wr_addr == $past(wr_addr)+1
  );
  assert property (@(posedge clk) disable iff (!rst_n)
    (!r_hs && !sol) |=> wr_addr == $past(wr_addr)
  );

  // img_width must be multiple of ADATA_PIXELS
  assert property (@(posedge clk) disable iff (!rst_n)
    sol |-> ((img_width & (ADATA_PIXELS-1)) == 0)
  );

  // RREADY equals 'in_burst' phase (single outstanding burst)
  // Checked via scoreboard variable
  assert property (@(posedge clk) disable iff (!rst_n)
    M_AXI_RREADY == in_burst
  );

  // Scoreboard
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      in_burst        <= 1'b0;
      in_line         <= 1'b0;
      beats_left_line <= '0;
      beats_left_burst<= '0;
      beats_per_line  <= '0;
      expect_araddr   <= '0;
    end else begin
      if (sol) begin
        in_line         <= 1'b1;
        beats_per_line  <= (img_width >> SHIFT);
        beats_left_line <= (img_width >> SHIFT);
        expect_araddr   <= line_addr;
      end

      if (ar_hs) begin
        // One burst at a time
        assert (!in_burst)
          else $error("AR issued while previous burst not completed");
        // AR field checks
        assert (M_AXI_ARSIZE  == ARSIZE_EXP)
          else $error("ARSIZE mismatch");
        assert (M_AXI_ARBURST == 2'b01)
          else $error("ARBURST must be INCR");
        assert (M_AXI_ARLOCK  == 1'b0);
        assert (M_AXI_ARCACHE == 4'b0000);
        assert (M_AXI_ARPROT  == 3'h0);
        assert (M_AXI_ARQOS   == 4'h0);
        assert (M_AXI_ARADDR[ARSIZE_EXP-1:0] == '0)
          else $error("ARADDR not aligned to data width");
        // Address sequencing
        assert (M_AXI_ARADDR == expect_araddr)
          else $error("Unexpected ARADDR");
        expect_araddr <= M_AXI_ARADDR + BURST_BYTES;

        // ARLEN range and per-line planning
        assert (M_AXI_ARLEN <= C_M_AXI_BURST_LEN-1);
        assert (beats_left_line != 0)
          else $error("AR issued with no beats remaining in line");

        if (beats_left_line >= C_M_AXI_BURST_LEN)
          assert (M_AXI_ARLEN == C_M_AXI_BURST_LEN-1)
            else $error("Non-final burst must be max length");
        else
          assert (M_AXI_ARLEN == beats_left_line-1)
            else $error("Final burst length incorrect");

        beats_left_burst <= M_AXI_ARLEN + 1;
        beats_left_line  <= beats_left_line - (M_AXI_ARLEN + 1);
        in_burst         <= 1'b1;
      end

      if (r_hs) begin
        assert (in_burst)
          else $error("R beat while no burst active");
        // No read errors allowed
        assert (M_AXI_RRESP[1] == 1'b0)
          else $error("Read response error detected");
        // RLAST must occur on the final beat of the burst
        assert ((beats_left_burst == 1) == M_AXI_RLAST)
          else $error("RLAST timing mismatch");

        if (beats_left_burst == 1) begin
          beats_left_burst <= 0;
          in_burst         <= 1'b0;
        end else begin
          beats_left_burst <= beats_left_burst - 1;
        end
      end

      if (end_of_line_pulse) begin
        assert (in_line) else $error("EOL pulse outside of a line");
        assert (!in_burst) else $error("EOL with burst still active");
        assert (beats_left_line == 0)
          else $error("EOL but beats remaining not zero");
        assert (wr_addr == (img_width >> SHIFT))
          else $error("wr_addr does not match beats-per-line at EOL");
        in_line <= 1'b0;
      end
    end
  end

  // Coverage
  // 1) Observe a single-burst line
  cover property (@(posedge clk) disable iff (!rst_n)
    sol && ((img_width >> SHIFT) <= C_M_AXI_BURST_LEN)
      ##[1:16] ar_hs && (M_AXI_ARLEN + 1 == (img_width >> SHIFT))
      ##[0:1024] end_of_line_pulse
  );

  // 2) Observe a multi-burst line with at least one max-length burst and a short final burst
  cover property (@(posedge clk) disable iff (!rst_n)
    sol && ((img_width >> SHIFT) > C_M_AXI_BURST_LEN)
      ##[1:32] (ar_hs && (M_AXI_ARLEN == C_M_AXI_BURST_LEN-1))
      ##[1:2048] (ar_hs && (M_AXI_ARLEN != C_M_AXI_BURST_LEN-1))
      ##[0:1024] end_of_line_pulse
  );

  // 3) Observe RLAST on a read beat
  cover property (@(posedge clk) disable iff (!rst_n)
    r_hs && M_AXI_RLAST
  );

endmodule

bind line_reader line_reader_sva #(
  .C_IMG_WBITS(C_IMG_WBITS),
  .C_WRITE_INDEX_BITS(C_WRITE_INDEX_BITS),
  .C_M_AXI_BURST_LEN(C_M_AXI_BURST_LEN),
  .C_M_AXI_ADDR_WIDTH(C_M_AXI_ADDR_WIDTH),
  .C_M_AXI_DATA_WIDTH(C_M_AXI_DATA_WIDTH)
) line_reader_sva_i (.*);

`endif