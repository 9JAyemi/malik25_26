// SVA for cf_add: concise, high-quality checks and coverage
// Bind inside DUT to access internals
bind cf_add cf_add_sva #(.DELAY_DATA_WIDTH(DELAY_DATA_WIDTH)) cf_add_sva_i();

module cf_add_sva #(parameter int DELAY_DATA_WIDTH=16);
  localparam int DW = DELAY_DATA_WIDTH-1;

  // inside bound instance: direct access to clk, data_*, p*_*, data_p, ddata_*
  // minimal warm-up for $past
  logic v1, v2, v3, v4;
  always_ff @(posedge clk) begin
    v1 <= 1'b1;
    v2 <= v1;
    v3 <= v2;
    v4 <= v3;
  end

  function automatic [24:0] abs25(input [24:0] d);
    abs25 = d[24] ? (~{1'b0,d[23:0]} + 25'd1) : {1'b0,d[23:0]};
  endfunction

  // Stage-1 capture and absolute value correctness
  assert property (@(posedge clk) v1 |-> p1_ddata == $past(ddata_in));
  assert property (@(posedge clk) v1 |-> p1_data_1 == $past(abs25(data_1)));
  assert property (@(posedge clk) v1 |-> p1_data_2 == $past(abs25(data_2)));
  assert property (@(posedge clk) v1 |-> p1_data_3 == $past(abs25(data_3)));
  assert property (@(posedge clk) v1 |-> p1_data_4 == $past(abs25(data_4)));
  assert property (@(posedge clk) v1 |-> !p1_data_1[24] && !p1_data_2[24] && !p1_data_3[24] && !p1_data_4[24]);

  // Stage-2 pipeline and pairwise sums (25-bit truncation as in RTL)
  assert property (@(posedge clk) v2 |-> p2_ddata  == $past(p1_ddata));
  assert property (@(posedge clk) v2 |-> p2_data_0 == $past(p1_data_1 + p1_data_2));
  assert property (@(posedge clk) v2 |-> p2_data_1 == $past(p1_data_3 + p1_data_4));

  // Stage-3 pipeline and final sum
  assert property (@(posedge clk) v3 |-> p3_ddata == $past(p2_ddata));
  assert property (@(posedge clk) v3 |-> p3_data  == $past(p2_data_0 + p2_data_1));

  // End-to-end arithmetic check across pipeline (keeps RTL truncation points)
  assert property (@(posedge clk) v3 |-> p3_data ==
                   ($past(abs25(data_1)+abs25(data_2),2) + $past(abs25(data_3)+abs25(data_4),2)));

  // ddata pipeline latency
  assert property (@(posedge clk) v3 |-> ddata_out == $past(ddata_in,3));

  // data_p mapping from p3_data (branch-by-branch)
  assert property (@(posedge clk) v3 && $past(p3_data[24]) |-> data_p == 8'h00);
  assert property (@(posedge clk) v3 && (!$past(p3_data[24]) && ($past(p3_data[23:20])==4'd0))
                   |-> data_p == $past(p3_data[19:12]));
  assert property (@(posedge clk) v3 && (!$past(p3_data[24]) && ($past(p3_data[23:20])!=4'd0))
                   |-> data_p == 8'hff);

  // No X on outputs after fill
  assert property (@(posedge clk) v3 |-> !$isunknown({ddata_out, data_p}));

  // Coverage: exercise key branches, overflow paths, and latency
  cover property (@(posedge clk) v3 && $past(p3_data[24]));                       // 0-clamp path
  cover property (@(posedge clk) v3 && !$past(p3_data[24]) && ($past(p3_data[23:20])==4'd0)); // pass-through path
  cover property (@(posedge clk) v3 && !$past(p3_data[24]) && ($past(p3_data[23:20])!=4'd0)); // 0xFF saturate
  cover property (@(posedge clk) v3 && $changed(ddata_in) ##3 (ddata_out == $past(ddata_in,3)));

  // Exercise sign handling and addition overflow at intermediate stages
  cover property (@(posedge clk) data_1[24]);  cover property (@(posedge clk) data_2[24]);
  cover property (@(posedge clk) data_3[24]);  cover property (@(posedge clk) data_4[24]);
  cover property (@(posedge clk) p2_data_0[24]); cover property (@(posedge clk) p2_data_1[24]);
  cover property (@(posedge clk) p3_data[24]);

endmodule