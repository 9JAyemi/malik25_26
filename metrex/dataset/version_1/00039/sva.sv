// SVA checkers + binds for the provided RAM wrappers.
// Focus: data integrity across read/write, masked updates, X-checking, essential coverage.

package ram_sva_pkg;

  // Generic two-port (separate read/write clocks) masked RAM checker
  module tdp_mem_checker #(parameter int AW=1, DW=1, NSEG=1) (
    input  logic               W0_clk,
    input  logic [AW-1:0]      W0_addr,
    input  logic               W0_en,
    input  logic [DW-1:0]      W0_data,
    input  logic [NSEG-1:0]    W0_mask,

    input  logic               R0_clk,
    input  logic [AW-1:0]      R0_addr,
    input  logic               R0_en,
    input  logic [DW-1:0]      R0_data
  );
    localparam int SEG_W = (DW+NSEG-1)/NSEG;
    initial assert (DW % NSEG == 0) else $fatal(1, "DW must be divisible by NSEG");

    typedef logic [AW-1:0] addr_t;
    typedef logic [DW-1:0] data_t;

    // Shadow model using associative arrays to avoid huge memory
    data_t model_data [addr_t];
    data_t known_bits [addr_t];  // 1-bit per data bit indicates "known" tracked by model

    // Helper to expand segment mask bits into DW-bit mask
    function automatic data_t segmask_expand(input logic [NSEG-1:0] seg_en);
      data_t m = '0;
      for (int i=0;i<NSEG;i++) begin
        for (int j=0;j<SEG_W;j++) begin
          m[i*SEG_W + j] = seg_en[i];
        end
      end
      return m;
    endfunction

    // Safe getters (return zero if address not present)
    function automatic data_t get_known(input addr_t a);
      return known_bits.exists(a) ? known_bits[a] : '0;
    endfunction
    function automatic data_t get_data(input addr_t a);
      return model_data.exists(a) ? model_data[a] : '0;
    endfunction

    // Track read address register behavior
    addr_t rd_addr_q;
    logic  rd_seen;
    always_ff @(posedge R0_clk) begin
      if (R0_en) begin
        assert (!$isunknown({R0_en,R0_addr})) else $error("R0_en/addr X");
        rd_addr_q <= R0_addr;
        rd_seen   <= 1'b1;
      end
    end

    // Writes update model (masked)
    always_ff @(posedge W0_clk) begin
      if (W0_en) begin
        assert (!$isunknown({W0_en,W0_addr,W0_mask,W0_data})) else $error("W0_* X during write");
        data_t bm = segmask_expand(W0_mask);
        data_t cur_d = get_data(W0_addr);
        data_t cur_k = get_known(W0_addr);
        model_data[W0_addr] = (cur_d & ~bm) | (W0_data & bm);
        known_bits[W0_addr] = cur_k | bm;
      end
    end

    // Read data must match model for known bits; learn unknown bits on first observation
    always_ff @(posedge R0_clk) begin
      if (rd_seen) begin
        data_t kb = get_known(rd_addr_q);
        data_t md = get_data(rd_addr_q);
        // Assert known bits match and are not X
        assert (((R0_data & kb) === (md & kb))) else
          $error("Read mismatch @addr %0h: dut %0h model %0h mask %0h", rd_addr_q, R0_data, md, kb);
        assert (!$isunknown(R0_data & kb)) else
          $error("R0_data has X on known bits @addr %0h", rd_addr_q);
        // Learn remaining unknown bits from observed read
        if (kb != '1) begin
          model_data[rd_addr_q] <= (md & kb) | (R0_data & ~kb);
          known_bits[rd_addr_q] <= '1;
        end
      end
    end

    // Basic coverage
    cover property (@(posedge W0_clk) W0_en);
    cover property (@(posedge W0_clk) W0_en && (W0_mask != '0) && (W0_mask != {NSEG{1'b1}})); // partial
    cover property (@(posedge W0_clk) W0_en && (W0_mask == {NSEG{1'b1}})); // full
    cover property (@(posedge R0_clk) R0_en); // read handshake
    // Write then read same addr (best-effort, different clocks)
    sequence wr(addr_t a); @(posedge W0_clk) W0_en && (W0_addr==a) && (W0_mask!='0); endsequence
    sequence rd(addr_t a); @(posedge R0_clk) R0_en && (R0_addr==a); endsequence
    cover property (wr($) ##[1:10] rd($));

  endmodule

  // Generic single-port RW masked RAM checker
  module rw_masked_mem_checker #(parameter int AW=1, DW=1, NSEG=1) (
    input  logic               RW0_clk,
    input  logic [AW-1:0]      RW0_addr,
    input  logic               RW0_en,
    input  logic               RW0_wmode,         // 1=write, 0=read
    input  logic [NSEG-1:0]    RW0_wmask,
    input  logic [DW-1:0]      RW0_wdata,
    input  logic [DW-1:0]      RW0_rdata
  );
    localparam int SEG_W = (DW+NSEG-1)/NSEG;
    initial assert (DW % NSEG == 0) else $fatal(1, "DW must be divisible by NSEG");

    typedef logic [AW-1:0] addr_t;
    typedef logic [DW-1:0] data_t;

    data_t model_data [addr_t];
    data_t known_bits [addr_t];

    function automatic data_t segmask_expand(input logic [NSEG-1:0] seg_en);
      data_t m = '0;
      for (int i=0;i<NSEG;i++) begin
        for (int j=0;j<SEG_W;j++) begin
          m[i*SEG_W + j] = seg_en[i];
        end
      end
      return m;
    endfunction
    function automatic data_t get_known(input addr_t a);
      return known_bits.exists(a) ? known_bits[a] : '0;
    endfunction
    function automatic data_t get_data(input addr_t a);
      return model_data.exists(a) ? model_data[a] : '0;
    endfunction

    addr_t rd_addr_q;
    logic  rd_seen;

    always_ff @(posedge RW0_clk) begin
      assert (!$isunknown({RW0_en,RW0_wmode})) else $error("RW0_en/wmode X");
      if (RW0_en && RW0_wmode) begin
        assert (!$isunknown({RW0_addr,RW0_wmask,RW0_wdata})) else $error("RW write X inputs");
        data_t bm = segmask_expand(RW0_wmask);
        data_t cur_d = get_data(RW0_addr);
        data_t cur_k = get_known(RW0_addr);
        model_data[RW0_addr] = (cur_d & ~bm) | (RW0_wdata & bm);
        known_bits[RW0_addr] = cur_k | bm;
      end
      if (RW0_en && !RW0_wmode) begin
        assert (!$isunknown(RW0_addr)) else $error("RW read addr X");
        rd_addr_q <= RW0_addr;
        rd_seen   <= 1'b1;
      end
      if (rd_seen) begin
        data_t kb = get_known(rd_addr_q);
        data_t md = get_data(rd_addr_q);
        assert (((RW0_rdata & kb) === (md & kb))) else
          $error("RW read mismatch @addr %0h: dut %0h model %0h mask %0h", rd_addr_q, RW0_rdata, md, kb);
        assert (!$isunknown(RW0_rdata & kb)) else
          $error("RW0_rdata has X on known bits @addr %0h", rd_addr_q);
        if (kb != '1) begin
          model_data[rd_addr_q] <= (md & kb) | (RW0_rdata & ~kb);
          known_bits[rd_addr_q] <= '1;
        end
      end
    end

    // Coverage
    cover property (@(posedge RW0_clk) RW0_en && RW0_wmode); // write
    cover property (@(posedge RW0_clk) RW0_en && !RW0_wmode); // read
    cover property (@(posedge RW0_clk) RW0_en && RW0_wmode && (RW0_wmask != '0) && (RW0_wmask != {NSEG{1'b1}})); // partial
    cover property (@(posedge RW0_clk) RW0_en && RW0_wmode && (RW0_wmask == {NSEG{1'b1}})); // full
    // Write then read same address
    cover property (@(posedge RW0_clk)
      (RW0_en && RW0_wmode, addr=RW0_addr) ##1 (RW0_en && !RW0_wmode && RW0_addr==addr));

  endmodule

  // Single-port RW unmasked full-width write checker
  module rw_unmasked_mem_checker #(parameter int AW=1, DW=1) (
    input  logic               RW0_clk,
    input  logic [AW-1:0]      RW0_addr,
    input  logic               RW0_en,
    input  logic               RW0_wmode,         // 1=write, 0=read
    input  logic [DW-1:0]      RW0_wdata,
    input  logic [DW-1:0]      RW0_rdata
  );
    typedef logic [AW-1:0] addr_t;
    typedef logic [DW-1:0] data_t;

    data_t model_data [addr_t];
    data_t known_bits [addr_t];

    function automatic data_t get_known(input addr_t a);
      return known_bits.exists(a) ? known_bits[a] : '0;
    endfunction
    function automatic data_t get_data(input addr_t a);
      return model_data.exists(a) ? model_data[a] : '0;
    endfunction

    addr_t rd_addr_q;
    logic  rd_seen;

    always_ff @(posedge RW0_clk) begin
      assert (!$isunknown({RW0_en,RW0_wmode})) else $error("RW0_en/wmode X");
      if (RW0_en && RW0_wmode) begin
        assert (!$isunknown({RW0_addr,RW0_wdata})) else $error("RW write X inputs");
        model_data[RW0_addr] = RW0_wdata;
        known_bits[RW0_addr] = '1;
      end
      if (RW0_en && !RW0_wmode) begin
        assert (!$isunknown(RW0_addr)) else $error("RW read addr X");
        rd_addr_q <= RW0_addr;
        rd_seen   <= 1'b1;
      end
      if (rd_seen) begin
        data_t kb = get_known(rd_addr_q);
        data_t md = get_data(rd_addr_q);
        assert (((RW0_rdata & kb) === (md & kb))) else
          $error("RW read mismatch @addr %0h: dut %0h model %0h", rd_addr_q, RW0_rdata, md);
        assert (!$isunknown(RW0_rdata & kb)) else
          $error("RW0_rdata has X on known bits @addr %0h", rd_addr_q);
        if (kb != '1) begin
          model_data[rd_addr_q] <= (md & kb) | (RW0_rdata & ~kb);
          known_bits[rd_addr_q] <= '1;
        end
      end
    end

    // Coverage
    cover property (@(posedge RW0_clk) RW0_en && RW0_wmode);
    cover property (@(posedge RW0_clk) RW0_en && !RW0_wmode);
    cover property (@(posedge RW0_clk)
      (RW0_en && RW0_wmode, addr=RW0_addr) ##1 (RW0_en && !RW0_wmode && RW0_addr==addr));

  endmodule

endpackage

// Bind the checkers to the DUTs

import ram_sva_pkg::*;

// _T_146_ext: 6b addr, 88b data, 4 segments (22b each)
bind _T_146_ext tdp_mem_checker #(.AW(6),  .DW(88), .NSEG(4)) _chk_T146 (
  .W0_clk(W0_clk), .W0_addr(W0_addr), .W0_en(W0_en), .W0_data(W0_data), .W0_mask(W0_mask),
  .R0_clk(R0_clk), .R0_addr(R0_addr), .R0_en(R0_en), .R0_data(R0_data)
);

// _T_80_ext: 9b addr, 64b data, 1 segment (mask[0])
bind _T_80_ext tdp_mem_checker #(.AW(9),  .DW(64), .NSEG(1)) _chk_T80 (
  .W0_clk(W0_clk), .W0_addr(W0_addr), .W0_en(W0_en), .W0_data(W0_data), .W0_mask(W0_mask),
  .R0_clk(R0_clk), .R0_addr(R0_addr), .R0_en(R0_en), .R0_data(R0_data)
);

// mem_0_ext: 9b addr, 64b data, 8 byte segments
bind mem_0_ext tdp_mem_checker #(.AW(9),  .DW(64), .NSEG(8)) _chk_mem0 (
  .W0_clk(W0_clk), .W0_addr(W0_addr), .W0_en(W0_en), .W0_data(W0_data), .W0_mask(W0_mask),
  .R0_clk(R0_clk), .R0_addr(R0_addr), .R0_en(R0_en), .R0_data(R0_data)
);

// mem_ext: 25b addr, 64b data, 8 byte segments (associative model keeps it light)
bind mem_ext tdp_mem_checker #(.AW(25), .DW(64), .NSEG(8)) _chk_mem (
  .W0_clk(W0_clk), .W0_addr(W0_addr), .W0_en(W0_en), .W0_data(W0_data), .W0_mask(W0_mask),
  .R0_clk(R0_clk), .R0_addr(R0_addr), .R0_en(R0_en), .R0_data(R0_data)
);

// tag_array_ext: single-port RW, 6b addr, 80b data, 4 segments
bind tag_array_ext rw_masked_mem_checker #(.AW(6), .DW(80), .NSEG(4)) _chk_tag (
  .RW0_clk(RW0_clk), .RW0_addr(RW0_addr), .RW0_en(RW0_en), .RW0_wmode(RW0_wmode),
  .RW0_wmask(RW0_wmask), .RW0_wdata(RW0_wdata), .RW0_rdata(RW0_rdata)
);

// _T_850_ext: single-port RW, 9b addr, 64b data, full-width writes
bind _T_850_ext rw_unmasked_mem_checker #(.AW(9), .DW(64)) _chk_T850 (
  .RW0_clk(RW0_clk), .RW0_addr(RW0_addr), .RW0_en(RW0_en), .RW0_wmode(RW0_wmode),
  .RW0_wdata(RW0_wdata), .RW0_rdata(RW0_rdata)
);