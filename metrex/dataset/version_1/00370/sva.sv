// SystemVerilog Assertions for ad_ss_422to444
// Focus: pipeline alignment, chroma selector behavior, averaging correctness, output mapping, and key coverage

module ad_ss_422to444_sva
  #(parameter Cr_Cb_N = 0,
    parameter DELAY_DATA_WIDTH = 16,
    localparam DW = DELAY_DATA_WIDTH-1);

  // Access DUT signals directly via bind scope
  // clk, inputs/outputs, and internal regs/wires are in scope

  // Create valid flags for $past depth
  logic past1, past2, past3;
  initial begin past1 = 0; past2 = 0; past3 = 0; end
  always_ff @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
    past3 <= past2;
  end

  // 1) Pipeline alignment checks
  assert property (@(posedge clk) past1 |-> s422_de_d     == $past(s422_de));
  assert property (@(posedge clk) past1 |-> s422_sync_d   == $past(s422_sync));
  assert property (@(posedge clk) past1 |-> s422_Y_d      == $past(s422_data[7:0]));
  assert property (@(posedge clk) past1 |-> s422_CbCr_d   == $past(s422_data[15:8]));
  assert property (@(posedge clk) past2 |-> s422_de_2d    == $past(s422_de,2));
  assert property (@(posedge clk) past2 |-> s422_CbCr_2d  == $past(s422_data[15:8],2));

  assert property (@(posedge clk) past2 |-> s444_sync           == $past(s422_sync,2));
  assert property (@(posedge clk) past2 |-> s444_data[15:8]     == $past(s422_data[7:0],2));

  // 2) cr_cb_sel behavior (toggle in active DE, reset to Cr_Cb_N otherwise)
  assert property (@(posedge clk) past1 |-> cr_cb_sel == ($past(s422_de_d) ? ~$past(cr_cb_sel) : Cr_Cb_N));
  // Additionally, first sample of a DE burst must select Cr_Cb_N
  assert property (@(posedge clk) $rose(s422_de) |-> (cr_cb_sel == Cr_Cb_N));

  // 3) 9-bit averaging function correctness (detects truncation bugs)
  // Use true 9-bit add for the both-valid case
  assert property (@(posedge clk)
    s422_CbCr_avg ==
      ((s422_de && s422_de_2d) ? ({1'b0,s422_CbCr} + {1'b0,s422_CbCr_2d}) :
       (s422_de               ? {s422_CbCr,1'b0}   : {s422_CbCr_2d,1'b0})));

  // 4) Output mapping of Cb/Cr vs avg aligned to selection (note: selection is 2 cycles in the past)
  assert property (@(posedge clk) past2 |->
    s444_data[23:16] == ($past(cr_cb_sel,2) ? $past(s422_CbCr_d,2) : $past(s422_CbCr_avg[8:1],2)));
  assert property (@(posedge clk) past2 |->
    s444_data[7:0]   == ($past(cr_cb_sel,2) ? $past(s422_CbCr_avg[8:1],2) : $past(s422_CbCr_d,2)));

  // 5) Key coverage
  // Start of a DE burst
  cover property (@(posedge clk) $rose(s422_de));
  // Toggle within DE
  cover property (@(posedge clk) s422_de && $past(s422_de) && (cr_cb_sel == ~$past(cr_cb_sel)));
  // Averaging modes: both-valid, left-only, right-only
  cover property (@(posedge clk) (s422_de && s422_de_2d));       // both valid
  cover property (@(posedge clk) (s422_de && !s422_de_2d));      // only current valid
  cover property (@(posedge clk) (!s422_de && s422_de_2d));      // only 2d valid
  // Exercise carry in average (9th bit set)
  cover property (@(posedge clk) (s422_de && s422_de_2d && s422_CbCr_avg[8]));

endmodule

// Bind into the DUT (parameters are forwarded)
bind ad_ss_422to444 ad_ss_422to444_sva #(.Cr_Cb_N(Cr_Cb_N), .DELAY_DATA_WIDTH(DELAY_DATA_WIDTH)) u_ad_ss_422to444_sva();