// SVA for mode_write
// Bind this module to DUT: bind mode_write mode_write_sva sva(.clk(clk), .rstn(rstn), .*);

module mode_write_sva(
  input clk,
  input rstn,
  input [5:0] cnt,
  input [6:0] blockcnt,
  input [5:0] bestmode,
  input [5:0] bestmode16,
  input [5:0] bestmode32,
  input finish,
  input md_we,
  input [5:0] md_wdata,
  input [6:0] md_waddr
);

  default clocking cb @(posedge clk); endclocking
  // Use disable iff for sequential checks; keep explicit reset checks separate

  // Combinational condition that defines md_we
  wire cond_we =
       ((blockcnt > 7'd1) && (cnt == 6'd11))
    || ((blockcnt[1:0] == 2'b01) && (cnt == 6'd12) && (blockcnt != 7'd1))
    || ((blockcnt[3:0] == 4'b0001) && (cnt == 6'd13) && (blockcnt != 7'd1));

  // Reset value checks (asynchronous reset is level-sensitive)
  assert property (@(posedge clk) !rstn |-> (md_waddr == 7'd0 && md_we == 1'b0 && md_wdata == 6'd0));

  // No X on outputs after reset released
  assert property (disable iff (!rstn) !$isunknown({md_we, md_waddr, md_wdata}));

  // md_we must equal its defining condition (both directions in one equality)
  assert property (disable iff (!rstn) md_we == cond_we);

  // Address behavior
  // Increment on md_we (wrap at 127)
  assert property (disable iff (!rstn)
    md_we |-> (md_waddr == (($past(md_waddr)==7'h7F) ? 7'h00 : $past(md_waddr)+7'd1))
  );
  // Reset to 0 on finish when no write
  assert property (disable iff (!rstn)
    (finish && !md_we) |-> (md_waddr == 7'd0)
  );
  // Hold otherwise
  assert property (disable iff (!rstn)
    (!md_we && !finish) |-> (md_waddr == $past(md_waddr))
  );

  // Data muxing behavior
  assert property (disable iff (!rstn) (cnt == 6'd11) |-> (md_wdata == bestmode));
  assert property (disable iff (!rstn) (cnt == 6'd12) |-> (md_wdata == bestmode16));
  assert property (disable iff (!rstn) (cnt == 6'd13) |-> (md_wdata == bestmode32));
  assert property (disable iff (!rstn) !(cnt inside {6'd11,6'd12,6'd13}) |-> (md_wdata == $past(md_wdata)));

  // When a write occurs, data must match the selected source for that count
  assert property (disable iff (!rstn)
    md_we |->
      ((cnt==6'd11 && md_wdata==bestmode) ||
       (cnt==6'd12 && md_wdata==bestmode16) ||
       (cnt==6'd13 && md_wdata==bestmode32))
  );

  // ----------------------------------
  // Coverage
  // ----------------------------------
  // Cover each write-enable path
  cover property (disable iff (!rstn) (cnt==6'd11 && blockcnt>7'd1 && md_we));
  cover property (disable iff (!rstn) (cnt==6'd12 && blockcnt[1:0]==2'b01 && blockcnt!=7'd1 && md_we));
  cover property (disable iff (!rstn) (cnt==6'd13 && blockcnt[3:0]==4'b0001 && blockcnt!=7'd1 && md_we));

  // Cover finish with and without concurrent write (priority check is inherent)
  cover property (disable iff (!rstn) (finish && !md_we && md_waddr==7'd0));
  cover property (disable iff (!rstn)
    $past(md_waddr)!=7'h7F && (finish && md_we) ##0 (md_waddr == $past(md_waddr)+7'd1)
  );

  // Cover address wrap on write
  cover property (disable iff (!rstn)
    ($past(md_waddr)==7'h7F && md_we) ##0 (md_waddr==7'h00)
  );

  // Cover data writes for all three modes
  cover property (disable iff (!rstn) md_we && cnt==6'd11 && md_wdata==bestmode);
  cover property (disable iff (!rstn) md_we && cnt==6'd12 && md_wdata==bestmode16);
  cover property (disable iff (!rstn) md_we && cnt==6'd13 && md_wdata==bestmode32);

endmodule

// Bind into the DUT
bind mode_write mode_write_sva sva(.clk(clk), .rstn(rstn), .*);