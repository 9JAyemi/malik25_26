// SVA checker for mux_parity_add
module mux_parity_add_sva (
  input  [2:0] sel,
  input  [3:0] data0,
  input  [3:0] data1,
  input  [3:0] data2,
  input  [3:0] data3,
  input  [3:0] data4,
  input  [3:0] data5,
  input  [3:0] out,
  input        parity
);

  // Sample on any relevant combinational change
  event comb_ev;
  always @(sel or data0 or data1 or data2 or data3 or data4 or data5 or out or parity) -> comb_ev;

  // Recompute expected behavior
  function automatic [3:0] pick(input [2:0] s,
                                input [3:0] d0, input [3:0] d1, input [3:0] d2,
                                input [3:0] d3, input [3:0] d4, input [3:0] d5);
    case (s)
      3'b000: pick = d0;
      3'b001: pick = d1;
      3'b010: pick = d2;
      3'b011: pick = d3;
      3'b100: pick = d4;
      3'b101: pick = d5;
      default: pick = 4'b0000;
    endcase
  endfunction

  wire [3:0] sd      = pick(sel, data0, data1, data2, data3, data4, data5);
  wire [1:0] ar      = sd[1:0] - sd[3:2];          // 2-bit modular subtraction
  wire [3:0] exp_out = {ar, sd[3:2]};
  wire       exp_par = ~^exp_out;

  // Functional correctness
  a_out:     assert property (@(comb_ev) out    === exp_out);
  a_parity:  assert property (@(comb_ev) parity === (~^out));

  // Default branch behavior (including X/Z on sel)
  a_default: assert property (@(comb_ev)
                              (sel inside {3'b110,3'b111} || $isunknown(sel))
                              |-> (out === 4'b0000 && parity === 1'b1));

  // No-X on outputs when selected inputs are fully known
  a_no_x:    assert property (@(comb_ev)
                              (!$isunknown(sel) && !$isunknown(sd))
                              |-> (!$isunknown({out,parity})));

  // Combinational determinism (no unintended state)
  a_stable:  assert property (@(comb_ev)
                              $stable({sel,data0,data1,data2,data3,data4,data5})
                              |-> $stable({out,parity}));

  // Coverage
  genvar i;
  generate
    for (i=0; i<6; i++) begin : g_sel_cov
      cover property (@(comb_ev) sel == i[2:0]);
    end
  endgenerate
  cover property (@(comb_ev) sel inside {3'b110,3'b111}); // default path taken
  cover property (@(comb_ev) parity == 1'b0);
  cover property (@(comb_ev) parity == 1'b1);
  cover property (@(comb_ev) (sd[1:0] <  sd[3:2])); // wrap-around subtract
  cover property (@(comb_ev) (sd[1:0] >= sd[3:2])); // non-wrap subtract

endmodule

// Bind into DUT
bind mux_parity_add mux_parity_add_sva sva (
  .sel(sel),
  .data0(data0), .data1(data1), .data2(data2),
  .data3(data3), .data4(data4), .data5(data5),
  .out(out),
  .parity(parity)
);