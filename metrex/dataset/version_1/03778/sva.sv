// SVA for top_module
module top_module_sva (
    input        clk,
    input        a,
    input        b,
    input        sel_b1,
    input        sel_b2,
    input  [2:0] sel, 
    input  [3:0] data0,
    input  [3:0] data1,
    input  [3:0] data2,
    input  [3:0] data3,
    input  [3:0] data4,
    input  [3:0] data5,
    input  [7:0] sum_out,
    input        out_2to1_mux,
    input  [3:0] out_6to1_mux
);
  default clocking cb @ (posedge clk); endclocking

  // 2:1 registered mux correctness (observed next cycle due to SVA sampling/NBA)
  property p_out2_updates;
    1 |=> out_2to1_mux == $past((sel_b1 && sel_b2) ? b : a);
  endproperty
  a_out2_updates: assert property (p_out2_updates);

  // Sum pipeline correctness (sum_out captures old out_2to1_mux + current out_6to1_mux)
  property p_sum_correct;
    1 |=> sum_out == $past(out_2to1_mux) + $past(out_6to1_mux);
  endproperty
  a_sum_correct: assert property (p_sum_correct);

  // Sum must fit in 5 bits (redundant with p_sum but cheap sanity)
  a_sum_narrow: assert property (1 |=> sum_out[7:5] == 3'b000);

  // 6:1 mux mapping (sampled on clk to avoid comb races)
  a_mux6_000:     assert property (sel == 3'b000 |-> out_6to1_mux == data0);
  a_mux6_001:     assert property (sel == 3'b001 |-> out_6to1_mux == data1);
  a_mux6_002:     assert property (sel == 3'b010 |-> out_6to1_mux == data2);
  a_mux6_003:     assert property (sel == 3'b011 |-> out_6to1_mux == data3);
  a_mux6_004:     assert property (sel == 3'b100 |-> out_6to1_mux == data4);
  a_mux6_005:     assert property (sel == 3'b101 |-> out_6to1_mux == data5);
  a_mux6_default: assert property (sel inside {3'b110,3'b111} |-> out_6to1_mux == data0);

  // Coverage: exercise all 6:1 selections (incl. default), 2:1 select combos, and sum extremes
  c_sel_000:      cover property (sel == 3'b000);
  c_sel_001:      cover property (sel == 3'b001);
  c_sel_002:      cover property (sel == 3'b010);
  c_sel_003:      cover property (sel == 3'b011);
  c_sel_004:      cover property (sel == 3'b100);
  c_sel_005:      cover property (sel == 3'b101);
  c_sel_default:  cover property (sel inside {3'b110,3'b111});

  c_selb_00:      cover property (sel_b1 == 0 && sel_b2 == 0);
  c_selb_01:      cover property (sel_b1 == 0 && sel_b2 == 1);
  c_selb_10:      cover property (sel_b1 == 1 && sel_b2 == 0);
  c_selb_11:      cover property (sel_b1 == 1 && sel_b2 == 1);

  c_sum_zero:     cover property ((out_2to1_mux == 1'b0 && out_6to1_mux == 4'h0) |=> sum_out == 8'h00);
  c_sum_16:       cover property ((out_2to1_mux == 1'b1 && out_6to1_mux == 4'hF) |=> sum_out == 8'h10);
endmodule

bind top_module top_module_sva sva_i (.*);