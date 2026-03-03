// SVA checkers and binds for mux_4to1_and and mux2to1

// 2:1 mux checker (bound to every mux2to1)
module mux2to1_sva #(parameter W=4)
(
  input logic [W-1:0] a, b, y,
  input logic         sel
);
  // Functional correctness
  a_func: assert property (@*) (y === (sel ? b : a));

  // Basic selection coverage
  c_sel0: cover  property (@*) (!sel && (y === a));
  c_sel1: cover  property (@*) ( sel && (y === b));

  // Output activity coverage
  genvar i;
  generate
    for (i=0;i<W;i++) begin : g_tog
      c_rise: cover property (@*) $rose(y[i]);
      c_fall: cover property (@*) $fell(y[i]);
    end
  endgenerate
endmodule

// 4:1 mux (end-to-end) checker
module mux_4to1_and_sva #(parameter W=4)
(
  input logic [W-1:0] a, b, c, d, y,
  input logic [1:0]   sel
);
  // End-to-end decode mapping (covers full functionality incl. no unintended ANDing)
  a_sel00: assert property (@*) ((sel == 2'b00) |-> (y === a));
  a_sel01: assert property (@*) ((sel == 2'b01) |-> (y === b));
  a_sel10: assert property (@*) ((sel == 2'b10) |-> (y === c));
  a_sel11: assert property (@*) ((sel == 2'b11) |-> (y === d));

  // Selection coverage
  c_00: cover property (@*) (sel == 2'b00 && y === a);
  c_01: cover property (@*) (sel == 2'b01 && y === b);
  c_10: cover property (@*) (sel == 2'b10 && y === c);
  c_11: cover property (@*) (sel == 2'b11 && y === d);
endmodule

// Bind checkers
bind mux2to1       mux2to1_sva      #(.W(4)) b_mux2_chk (.*);
bind mux_4to1_and  mux_4to1_and_sva #(.W(4)) b_mux4_chk (.*);