// SVA checkers + binds for EFX_*

// ------------------------------------------------------------
// EFX_LUT4
// ------------------------------------------------------------
module EFX_LUT4_sva #(parameter LUTMASK = 16'h0000) (
  input I0, input I1, input I2, input I3, input O
);
  wire [3:0] addr = {I3,I2,I1,I0};

  // Functional equivalence
  assert property (@(I0 or I1 or I2 or I3) O === LUTMASK[addr])
    else $error("EFX_LUT4: O != LUTMASK[{I3,I2,I1,I0}]");

  // Coverage: all 16 address selections + O activity
  genvar a;
  generate for (a=0; a<16; a++) begin : g_addr_cov
    localparam [3:0] A = a[3:0];
    cover property (@(I0 or I1 or I2 or I3) addr==A);
  end endgenerate
  cover property (@(I0 or I1 or I2 or I3) $changed(O));
endmodule

bind EFX_LUT4 EFX_LUT4_sva #(.LUTMASK(LUTMASK)) EFX_LUT4_sva_i (.*);

// ------------------------------------------------------------
// EFX_ADD
// ------------------------------------------------------------
module EFX_ADD_sva #(parameter I0_POLARITY=1, parameter I1_POLARITY=1) (
  input I0, input I1, input CI, input O, input CO
);
  wire i0 = I0_POLARITY ? I0 : ~I0;
  wire i1 = I1_POLARITY ? I1 : ~I1;

  // Functional equivalence (sum and carry)
  assert property (@(I0 or I1 or CI) {CO,O} === (i0 + i1 + CI))
    else $error("EFX_ADD: {CO,O} mismatch");

  // Coverage: all input combinations, O/CO activity
  genvar k;
  generate for (k=0; k<8; k++) begin : g_in_cov
    localparam [2:0] K = k[2:0];
    cover property (@(I0 or I1 or CI) {I0,I1,CI}==K);
  end endgenerate
  cover property (@(I0 or I1 or CI) $changed({CO,O}));
endmodule

bind EFX_ADD EFX_ADD_sva #(.I0_POLARITY(I0_POLARITY), .I1_POLARITY(I1_POLARITY)) EFX_ADD_sva_i (.*);

// ------------------------------------------------------------
// EFX_FF
// ------------------------------------------------------------
module EFX_FF_sva #(
  parameter CLK_POLARITY = 1,
  parameter CE_POLARITY  = 1,
  parameter SR_POLARITY  = 1,
  parameter SR_SYNC      = 0,
  parameter SR_VALUE     = 0,
  parameter SR_SYNC_PRIORITY = 0,
  parameter D_POLARITY   = 1
)(
  input CLK, input CE, input SR, input D, input Q
);
  wire clk = CLK_POLARITY ? CLK : ~CLK;
  wire ce  = CE_POLARITY  ? CE  : ~CE;
  wire sr  = SR_POLARITY  ? SR  : ~SR;
  wire d   = D_POLARITY   ? D   : ~D;

  // Common covers
  cover property (@(posedge clk) $changed(Q));

  generate
    if (SR_SYNC==1) begin : g_sync_sr
      if (SR_SYNC_PRIORITY==1) begin : g_prio_sr
        // SR has priority regardless of CE
        assert property (@(posedge clk) sr |-> (Q == SR_VALUE))
          else $error("EFX_FF(sync,prio): SR did not set Q");
        assert property (@(posedge clk) (!sr && ce) |-> (Q == d))
          else $error("EFX_FF(sync,prio): CE load failed");
        assert property (@(posedge clk) (!sr && !ce) |-> (Q == $past(Q)))
          else $error("EFX_FF(sync,prio): Q not held when CE=0");
        cover property (@(posedge clk) sr);
        cover property (@(posedge clk) (!sr && ce));
        cover property (@(posedge clk) (!sr && !ce));
      end else begin : g_prio_ce
        // CE gating: update only when CE=1
        assert property (@(posedge clk) (ce && sr) |-> (Q == SR_VALUE))
          else $error("EFX_FF(sync,ce-prio): SR did not set Q when CE=1");
        assert property (@(posedge clk) (ce && !sr) |-> (Q == d))
          else $error("EFX_FF(sync,ce-prio): CE load failed");
        assert property (@(posedge clk) (!ce) |-> (Q == $past(Q)))
          else $error("EFX_FF(sync,ce-prio): Q not held when CE=0");
        cover property (@(posedge clk) (ce && sr));
        cover property (@(posedge clk) (ce && !sr));
        cover property (@(posedge clk) (!ce));
      end
    end else begin : g_async_sr
      // Asynchronous SR assertion
      assert property (@(posedge sr) 1 |=> (Q == SR_VALUE))
        else $error("EFX_FF(async): SR did not asynchronously set Q");
      // While SR held high, Q stays at SR_VALUE across clocks
      assert property (@(posedge clk) sr |-> (Q == SR_VALUE))
        else $error("EFX_FF(async): Q changed while SR asserted");
      // Normal clocked update when SR deasserted
      assert property (@(posedge clk) (!sr && ce) |-> (Q == d))
        else $error("EFX_FF(async): CE load failed");
      assert property (@(posedge clk) (!sr && !ce) |-> (Q == $past(Q)))
        else $error("EFX_FF(async): Q not held when CE=0 and SR=0");
      cover property (@(posedge sr) 1);
      cover property (@(posedge clk) (!sr && ce));
      cover property (@(posedge clk) (!sr && !ce));
    end
  endgenerate
endmodule

bind EFX_FF EFX_FF_sva #(
  .CLK_POLARITY(CLK_POLARITY),
  .CE_POLARITY (CE_POLARITY),
  .SR_POLARITY (SR_POLARITY),
  .SR_SYNC     (SR_SYNC),
  .SR_VALUE    (SR_VALUE),
  .SR_SYNC_PRIORITY(SR_SYNC_PRIORITY),
  .D_POLARITY  (D_POLARITY)
) EFX_FF_sva_i (.*);

// ------------------------------------------------------------
// EFX_GBUFCE
// ------------------------------------------------------------
module EFX_GBUFCE_sva #(parameter CE_POLARITY=1'b1) (
  input CE, input I, input O
);
  wire ce = CE_POLARITY ? CE : ~CE;

  // Functional equivalence
  assert property (@(I or CE) O === (I & ce))
    else $error("EFX_GBUFCE: O != I & ce");

  // Coverage: gate open/closed and O activity
  cover property (@(I or CE) ce);
  cover property (@(I or CE) !ce);
  cover property (@(I or CE) $changed(O));
endmodule

bind EFX_GBUFCE EFX_GBUFCE_sva #(.CE_POLARITY(CE_POLARITY)) EFX_GBUFCE_sva_i (.*);

// ------------------------------------------------------------
// EFX_RAM_5K  (structural/param checks + basic event coverage)
// ------------------------------------------------------------
module EFX_RAM_5K_sva #(
  parameter READ_WIDTH = 20,
  parameter WRITE_WIDTH = 20,
  parameter OUTPUT_REG = 1'b0,
  parameter RCLK_POLARITY  = 1'b1,
  parameter RE_POLARITY    = 1'b1,
  parameter WCLK_POLARITY  = 1'b1,
  parameter WE_POLARITY    = 1'b1,
  parameter WCLKE_POLARITY = 1'b1,
  parameter WRITE_MODE     = "READ_FIRST"
)(
  input [WRITE_WIDTH-1:0] WDATA,
  input [/*WADDR*/0:0] WADDR, // width checked via $bits
  input WE,
  input WCLK,
  input WCLKE,
  input [/*RADDR*/0:0] RADDR, // width checked via $bits
  input RE,
  input RCLK,
  input [READ_WIDTH-1:0] RDATA
);
  function automatic int map_width_to_addrw (int w);
    case (w)
      1:  map_width_to_addrw = 12;
      2:  map_width_to_addrw = 11;
      4:  map_width_to_addrw = 10;
      5:  map_width_to_addrw = 10;
      8:  map_width_to_addrw = 9;
      10: map_width_to_addrw = 9;
      16: map_width_to_addrw = 8;
      20: map_width_to_addrw = 8;
      default: map_width_to_addrw = -1;
    endcase
  endfunction

  initial begin
    // Legal widths and port width consistency
    assert (READ_WIDTH inside {1,2,4,5,8,10,16,20})
      else $error("EFX_RAM_5K: illegal READ_WIDTH=%0d", READ_WIDTH);
    assert (WRITE_WIDTH inside {1,2,4,5,8,10,16,20})
      else $error("EFX_RAM_5K: illegal WRITE_WIDTH=%0d", WRITE_WIDTH);
    assert ($bits(RADDR) == map_width_to_addrw(READ_WIDTH))
      else $error("EFX_RAM_5K: RADDR width mismatch (have %0d, exp %0d)", $bits(RADDR), map_width_to_addrw(READ_WIDTH));
    assert ($bits(WADDR) == map_width_to_addrw(WRITE_WIDTH))
      else $error("EFX_RAM_5K: WADDR width mismatch (have %0d, exp %0d)", $bits(WADDR), map_width_to_addrw(WRITE_WIDTH));
    assert ($bits(RDATA) == READ_WIDTH)
      else $error("EFX_RAM_5K: RDATA width mismatch");
    assert ($bits(WDATA) == WRITE_WIDTH)
      else $error("EFX_RAM_5K: WDATA width mismatch");
    assert (WRITE_MODE == "READ_FIRST" || WRITE_MODE == "WRITE_FIRST" || WRITE_MODE == "NO_CHANGE")
      else $error("EFX_RAM_5K: illegal WRITE_MODE=%s", WRITE_MODE);
  end

  // Derived effective controls
  wire rclk  = RCLK_POLARITY  ? RCLK  : ~RCLK;
  wire re_e  = RE_POLARITY    ? RE    : ~RE;
  wire wclk  = WCLK_POLARITY  ? WCLK  : ~WCLK;
  wire we_e  = WE_POLARITY    ? WE    : ~WE;
  wire wclke = WCLKE_POLARITY ? WCLKE : ~WCLKE;

  // Basic event coverage (writes and reads observed at effective edges)
  cover property (@(posedge wclk) (we_e && wclke));
  cover property (@(posedge rclk) (re_e));
endmodule

bind EFX_RAM_5K EFX_RAM_5K_sva #(
  .READ_WIDTH(READ_WIDTH),
  .WRITE_WIDTH(WRITE_WIDTH),
  .OUTPUT_REG(OUTPUT_REG),
  .RCLK_POLARITY(RCLK_POLARITY),
  .RE_POLARITY(RE_POLARITY),
  .WCLK_POLARITY(WCLK_POLARITY),
  .WE_POLARITY(WE_POLARITY),
  .WCLKE_POLARITY(WCLKE_POLARITY),
  .WRITE_MODE(WRITE_MODE)
) EFX_RAM_5K_sva_i (.*);